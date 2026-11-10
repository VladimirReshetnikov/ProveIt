# Sign24 conditional polynomial bridge staged check

This two-stage retry tests the source-only factoring in the sibling draft.
Stage one specializes generic transport to the sign24/sign25 expression
zero equivalence while assuming the sign25 polynomial bridge. Stage two
imports the sign25 bridge and discharges that assumption. This is a
different elaboration order under the same limits, not a claim that memory
use will improve; stage two still imports both dependency cones.

The prior concrete attempt exited 1 after a Lean interpreter memory exception
at `-M2800`. This retry uses the same provider-union survey and the same
`-M2800`, one-thread and 120-second limits, 4 GiB monitored RSS, 10 GiB
available-memory floor, and 5 GB free-disk precheck. The sign24 syntax
provider inherits the existing 4,000,000-heartbeat option; these source
stages add none. Direct provider observations are not a complete transitive
or dynamic ancestry trace.

The author no-Lean preflight exited 0 (`preflight-author-record.json`). The
prior failure has passed independent audit. After independent prelaunch review,
attempt 01's conditional stage compiled, but its second stage failed with an
interpreter memory exception; the author observed outer session `97690` exit 1.
See `attempt01/README.md`. The [independent terminal audit](../../reviews/nine-sharing-sign24-polynomial-bridge-staged-terminal-independent/README.md)
passed for that partial result; the packet and stage inputs are frozen.
