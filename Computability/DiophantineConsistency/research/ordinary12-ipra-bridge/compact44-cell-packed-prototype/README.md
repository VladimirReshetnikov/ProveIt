# Represented compact cell for fixed row and dummy bit

`CompactPackedCell.lean` defines `packedCell a d` as the represented block
sum of `cellDigit a d` with **8807 subdigits in radix `2^67`**. In every
model of IΣ₁, when `d ≤ 1`, the checked lemmas show:

* the cell is below `2^(67*8807)`;
* each subdigit at a position below 8807 is the corresponding local digit;
* the 943 selector positions, all 41 payload-copy positions, and position
  1063 have their specified values;
* the cell for row zero is positive.

This is an actual represented cell for each **fixed** pair of model
parameters. It does not by itself supply a Σ₁-definable cell word as the
parameters vary: that requires a uniform graph for the packed cell and a
definable row and dummy function. In particular, the row-zero lemma does not
establish that the actual word's origin has row zero. No low- or high-mask
safety, pulse safety, product or carry normalization, `PackingInput`, graph
zero, or internal iPRA derivation follows here.

Tool session `42831` exited 0 with no warning or `sorryAx`. The six named
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The first attempt stopped at the dependency scan because the runner named a
nonexistent provider path; that failure is retained under
`observations/attempt01`. The corrected bounded runner's direct dependency and
companion guards were unchanged in the successful `attempt02`; its source,
command, dependency listing, compiler log, object hash, and terminal receipt
are recorded there. It inherits the fixed-digit and other provider, package,
transitive, dynamic-loading, and between-observation ancestry limitations; it
is a single-author build, not a paired replay or independent closure audit.
