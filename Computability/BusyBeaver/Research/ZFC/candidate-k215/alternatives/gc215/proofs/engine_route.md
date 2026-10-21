# Optional engine half-row liberation

This is a separate, proven equivalent routing experiment. It does not change the final GC215 candidate.

The native table has exactly one incoming row to control 26:

`11 / 0 : write 0, move L, enter 26`.

Consequently, on every visit to 26 from control 0, its right neighbor is 0. This is true for every initial binary tape, without any well-formed-register hypothesis. Controls 134 and 194 have the common read-zero row `0 R 17`.

Replace only `26 / 0 : 0 R 134` by `26 / 0 : 0 R 194`. If 26 reads 0, both machines take two steps, leave the tape unchanged, move two cells right, and enter 17. If 26 reads 1, its unchanged row enters 38 after moving right. All other rows agree. Grouping each read-zero visit to 26 with the following step gives a positive-block simulation in both directions. Thus the optional variant has exactly the same halting behavior as GC215 on every initial tape from control 0.

The corresponding three-step segment beginning at `11 / 0` can now avoid 134 entirely. This discharges the protected engine obligation on `134 / 0` caused by this path and could make future decoder allocations more flexible. It does not permit arbitrary changes to that half-row: its remaining decoder uses still need to be reallocated and validated. The exact optional table, finite local checks, incoming-row census, and hashes are emitted by `check_engine_route.py`.
