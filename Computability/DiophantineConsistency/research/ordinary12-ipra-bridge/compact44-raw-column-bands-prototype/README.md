# Exploratory raw-column decoder bands

`RawColumnBands.flatten` identifies the full indexed carry raw column as the sum of the two rotated selector/copy bands, five explicit bare rotated digits and the temporal digit. `decoder_bands` applies the existing model band-decomposition theorem to each band. For n>0, k<n and `C<2^(67*n)`, it expresses the exact column as two separate weighted selector/copy decoder-shaped sums plus the five bare terms and the temporal digit. All source indices and rotations are retained.

Author-only session 32698 actually exited 0 without warnings or `sorryAx`; both reports use `propext`, `Classical.choice`, `Quot.sound`. Earlier sessions 13152, 65905 and 65628 actually exited 1; their exact sources, logs and failure-derived `sorryAx` reports are retained. The same author overlay and dependencies from 061591283c were used. This is exploratory evidence, not a paired replay or independent artifact audit.

This theorem does not select a graph witness or remove the temporal, bare or second-band terms. It does not establish row semantics, local decoder hypotheses, retained-K binding, machine equivalence or internal iPRA.
