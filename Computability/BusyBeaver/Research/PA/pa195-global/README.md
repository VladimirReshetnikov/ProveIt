# PA195 global native-table quotient

`PA195Global.lean` proves `PA195LocalQuotient.halts_iff_any_tape`: the
unfolded 202-control parent and the folded 195-control native table from the
PA195 archive halt under exactly the same circumstances when started at native
control 74, for any initial integer head position and any complete two-way
binary tape. Native halt control is 254. The proof combines the checked finite
local quotient, its arbitrary-tape simulation and incoming-history invariant,
the parent-control totality certificate, and a generic deterministic trace
comparison. All project modules in the dependency chain can be rebuilt and
checked with:

```sh
Computability/BusyBeaver/Research/PA/pa195-global/check.sh
```

Run this from the repository root. The script builds fresh Lean objects in a
temporary `/dev/shm` directory and deletes them on exit. The generated table
source and its archive binding can be reproduced separately using
`../pa195-quotient/generate.py`.

This theorem concerns standard-natural-number finite runs of the two native
control tables. The separately supplied dense PA195 table starts at control 0
and halts at 195; the finite certificate checks its rows against the native
state map, but this theorem does not yet provide a dense-table halting
conjugacy. It also does not prove the consistency equivalence or a theorem
internal to PRA or iPRA.
