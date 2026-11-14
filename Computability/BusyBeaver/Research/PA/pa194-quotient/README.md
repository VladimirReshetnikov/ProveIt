# PA194 finite quotient certificate

`PA194LocalQuotient.lean` checks the seven-fold local simulation from the
unfolded 201-state native table to the 194-state native table in the placed
`../docs/pa194_conpa_2026-11-13/construction/` packet. It also checks each dense PA194
transition against the native table under the supplied state map.

To regenerate and check the Lean certificate from the repository root, run:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194-quotient/generate.py
lake env lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194-quotient/PA194LocalQuotient.lean
```

The generator checks the published SHA-256 of the dense table, verifies the
dense/native mapping and row uniqueness. It reads the parent table, state map,
folds, and case durations from the packet and reconstructs the deduplicated
native child table from the dense table and state map. Every input and the
reconstructed table are pinned to their original archive member's SHA-256. The
Lean theorem independently checks the dense/native mapping, coverage of all
28 history/read-bit cases, and the simulated endpoint in each case. The
simulator rejects reads outside the two inspected cells. It also checks the
incoming-history condition for every parent row and checks projection for all
other parent transitions. Kernel checking reports only `propext` as an axiom.

This finite certificate alone is not a theorem about arbitrary full tapes,
model-length traces, halting equivalence, or consistency. Those require
separate lifting and iteration proofs.
