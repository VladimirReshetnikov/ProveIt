# Auxiliary Pell ordinate phase bound

`ordinate_bound` proves that a Pell ordinate `ycoord R b` is at least two
for arbitrary internal b when `R % 4 = 3`, using the internal recurrence's
time lower bound. This supplies the bound needed by the conditional auxiliary
positivity client once the construction's exact ordinate identity is bound;
that binding and the full adaptive witness map remain open.

Two fresh root builds against the previously replayed auxiliary client
provider `/tmp/adaptive13-construction-aux-client-h8k4qkac/lib` passed with
identical source, object and complete-log hashes. The axiom report contains
`propext`, `Classical.choice`, and `Quot.sound`. [Drivers, snapshots, logs,
provider inventories and states](adaptive-construction-aux-phase2011-replay/)
are retained. An upstream merge changed `ArithmeticCarrierRadix2011.lean`
after that provider was built; this receipt authenticates the earlier
dependency snapshot and requires a source-current downstream replay.
Foundation/packages and inherited project objects remain cache boundaries.

A later upstream merge changed the `ArithmeticBinomLegendre.lean` dependency.
This receipt authenticates its earlier population-provider snapshot; a
source-current downstream replay is required.
