# Attribution

- **Elliot Glazer**: the compact set theory K, its equiconsistency with ZFC, the K source
  program and the 230-state machine, with its Rocq proof
  ([`elliotglazer/k230-rocq`](https://github.com/elliotglazer/k230-rocq) at
  `3142e4dd980f0be12f4abb636c4ae2528afc17eb`). `ingredients/k230.tm` and
  `ingredients/sites230.json` are that repository's `machine/k230.tm` and
  `machine/sites230.json`, byte for byte. Their SHA-256 values equal the
  `machine_sha256` and `program_sites_sha256` recorded in its `provenance.json`.
  That repository asserts no repository-wide license, and these files are not
  relicensed here.
- **Mira-Cult**: original calculus, program and 254-state construction. **Jeff
  Ketchersid**: upstream Rocq verification. **Andrew James Wade**: compiler framework.
  Their notices are kept under `licenses/`.
- **Sources 101 and 102** of the ZFC closure-kernels host: the delayed erasure (fold 169
  into 80 with helper `91/1`).
- **ProveIt**: the 241-state engine that k230 inherits, the loop rotation with the 90/72
  fold (240-state step, commit `e5c2b3337e`), Source 103's runtime checker as placed in
  the host, and this composition: transferring both engine savings to k230, the
  startup lockstep map, and the checks recorded in `evidence/`.

No claim of historical priority beyond these specific compositions is made.
