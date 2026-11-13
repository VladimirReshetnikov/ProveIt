# Exploratory unified temporal source formulas

`TemporalSourceUnified.digit` proves the actual fractional or aligned temporal digit formula in every IΣ₁ model for n>0, t<n and X<2^(67*n), with `q=(E/67)%n`, `r=E%67` and source `j=cyc n t q`. The formula expresses the output digit as `(dig 67 X j * 2^r)%2^67 + dig 67 X (cyc n j 1)/2^(67−r)`. It combines all q/t comparisons and the aligned r=0 case, preserving cyclic wrap.

`TemporalSourcePredecessor.cyclic_commute` proves that internal cyclic subtractions commute for positive n. Its `predecessor` theorem uses that fact to express the temporal digit at `cyc n t 1` in terms of the first two cyclic predecessor digits of the same j. The predecessor theorem only needs n>0 and the word bound; it does not require t<n. No identification of the zero-padded next digit with a cyclic digit is made.

Author-only sessions 17435 and 93010 actually exited 0 without warnings or `sorryAx`; reports use `propext`, `Classical.choice`, and `Quot.sound`. Sessions 94647 and 48500 actually exited 1 with exact failed source/logs retained; both included warnings and failure-derived `sorryAx` reports that prove nothing. The same author overlay and source chain recorded in commits ffe7765fba, 81417adafb and 076701dc40 were used. This is exploratory evidence, not a paired replay or independent artifact audit.

The actual graph-selected clean target, half-radix predecessor, clean carry, graph-column decoding, retained-K binding and internal iPRA remain separate.
