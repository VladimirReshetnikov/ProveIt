# Historical 106 endpoint: fixed-port source provenance

The historical stage-079 67/106 endpoint's overlay currently resolves the
`CurrentKernelData2011` and `CurrentMaskData2011` objects to the earlier
`/tmp/ha87-full-transitive-p3xt6wra` build. Starting at
`DiophantineConsistency.CurrentKernelData2011`, that build's recorded
source-declared graph has 12 project modules and eight external imports.
This check verifies that every one of the 12 recorded historical source
snapshots has the same SHA-256 and the same recorded direct imports as the
corresponding fresh current14 source snapshot. It checks the historical
and fresh build receipts and the actual historical/fresh object hashes for
those 12 modules, and confirms the two historical overlay resolutions.

The historical endpoint provider object is pinned at
`79bf09c3051ad06f55abdd511c7310ccd795856f1275b6b23836f8b535e74122`;
the independently replayed stage-079 source matches the live source, as
documented in `../normalized106-historical-endpoint-client/`. In
particular the historical and fresh `CurrentKernelData2011` source hash is
`529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c`, and
the corresponding `CurrentMaskData2011` source hash is
`8e92c1f507bc250c31fb2671a921dfbef7a44ba643956f962cd64d9b50bd4582`.

All 12 compared historical/fresh **object hashes differ**. Source equality
does not justify interchanging or combining those objects. The eight
external dependencies, the stage-079 transitive load trace, indirect/dynamic
loading and transitive historical provider ancestry are not independently
replayed here. Current overlay resolution does not itself establish exactly
which transitive objects were loaded during stage 079. This is a
source-provenance comparison for the fixed-port construction; it is not a
formal theorem identifying the materialized JSON coefficient bytes with
the Lean tuple, and does not parse a PDF or prove the numerical degree.

The read-only checker exited 0 with stdout redirected to `result.json`;
it invokes no Lean process. To reproduce from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/normalized106-historical-port-source-provenance/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `29600f535c0e40823a21f22be5c696b59c718c2552e8e8fdd7450c2fba724f99` |
| `result.json` | `11096cdc8b7fb28074b53b1e64a275632eef4883de126b0d0f0bc991b73ebb7b` |
| `outer-terminal.json` | `ede299f578e43719e4e673307fd95b7626a05298b8e96e717f25746ec03234f3` |
