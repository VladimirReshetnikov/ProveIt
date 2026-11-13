# Base-only client attempt 01: failed

The observed runner attempt exited with status 1. Its `Current14LiteralPortsMF --deps` child exited 0 and the first Lean compilation exited 1, with both child sessions reported drained. The runner recorded status `FAILED`; the structured endpoint client was not compiled. The compile log reports one unsolved goal in `omega_eq`: the geometric sums called `G` and `geometricInt` were treated as different atoms by `ring`. Lean printed axiom reports for the other named lemmas; reports containing `sorryAx` reflect the unsolved goal and are not a proof of those lemmas.

`capture/` is a snapshot of the full isolated attempt directory, including both source copies, state, and all logs. Paths embedded in the copied state identify their original `/tmp` locations. This records a failed client check and does not claim an iPRA endpoint result. See also the independently preserved review at `reviews/current14-mf-base-only-attempt01-failure/`.
