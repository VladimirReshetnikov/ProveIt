# PA195 finite quotient certificate

`PA195LocalQuotient.lean` checks the seven-fold local simulation from the
unfolded 202-state native table to the 195-state native table in the placed
`../docs/pa195_conpa_2026-11-13/pa195/` packet. It also checks each dense PA195
transition against the native table under the supplied state map.

To regenerate and check the Lean certificate from the repository root, run:

```sh
python3 Computability/BusyBeaver/Research/PA/pa195-quotient/generate.py
lake env lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa195-quotient/PA195LocalQuotient.lean
```

The generator checks the published SHA-256 of the dense table, verifies the
dense/native mapping and row uniqueness, and extracts both complete native
tables, the state map, folds, and local case durations from the packet, with
each input pinned to the original archive member's SHA-256. The
Lean theorem independently checks the dense/native mapping, coverage of all
28 history/read-bit cases, and the simulated endpoint in each case. The
simulator rejects reads outside the two inspected cells. It also checks the
incoming-history condition for every parent row and checks projection for all
other parent transitions. Kernel checking reports only `propext` as an axiom.

This finite certificate alone is not a theorem about arbitrary full tapes,
model-length traces, halting equivalence, or consistency. Those require
separate lifting and iteration proofs.
