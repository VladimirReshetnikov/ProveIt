# Independent adversarial audit

**Verdict: PASS**

Date: 2026-10-03. Scope: the fixed U15 finite-tape-pair to ordinary threshold-six Z^3 periodic-sandpile construction in the exact files hashed below. No outstanding mathematical or executable defect was found after the corrections listed here. This is an independent mathematical/code review with finite executable checks, not a machine-checked proof assistant certificate.

## Mathematical findings

- The explicit seven-segment router has globally separated support, including different gadgets, equal-x shafts in different rows, all x/y seams and the z seam. The proof establishes support degree at most 3 and exterior co-degree at most 2 for the infinite union; it does not extrapolate those claims solely from small examples.
- The first-forbidden-event argument proves that every support vertex topples at most once and exterior vertices never topple under every legal sequential history. The loader adds exactly one nonnegative chip at each of finitely many distinct height-5 roots. Liveness and equality with the least activation closure correctly use fair complete histories.
- The all-port gate contracts include backward output activation. The closed-upper-set/finite-derivation composition argument prevents reverse activation from manufacturing false state roots. FORK regions carry one signal; receiving input diodes isolate distinct signals. Unseeded negative-time cells and other z slabs remain inactive.
- The ten literal CA rule families simulate the pinned partial U15 table on every permitted finite pair. The shrinking-wing induction includes the final one- and two-cell cases and proves exact extinction. Partial failed AND computations are charged to active predecessor roots, with a one-row/two-cell collar; they do not create unbounded post-halt activity.
- Gate and edge numbering, the coefficient evaluator and binary input parser are finite explicit algorithms. The evaluator recovers a shaft's source residues from its unique incidence and a planar route's edge/residue from its height; integer ceiling/floor tests give exact modular segment membership. No truth-table synthesis, embedding, routing or background-coefficient oracle is assumed.
- Recomputed constants agree: N=3,879,975, M=5,819,945, B=186,238,848, Zmax=1,955,501,572, maximum route-edge bound 4,655,958,568 and support-per-period upper bound 758,727,842,139,046,136. The fixed-thickness active-prism constant is C=5,426,111,451,172,075,939,316,367,360 multiplying (n+T+1)^2. This pays for initialization, shutdown and partial gates.

## Independently executed checks

- All 28 gate activation subsets, forward and reverse legal orders, complete exterior halo; additional AND/OR checks at tail lengths 12 and 16, alongside the initial length-8 checks. The final length-12 receipt matches its generator exactly.
- All 5,819,945 universal-cell edge records and port incidences; final manifest equality, including an optimized-Python rerun. Canonical edge-stream SHA256 is 8b58cbb47f54031471a6bec48b02002ff401885eb29ab9e36a2e1c556facb4b5.
- Full literal-rule CA suite: 388,146 distinct patterns, 58 initializations, 4,335 updates and nine halting cases, with a final optimized-Python rerun using the bundled pure transition data.
- Both supplied complete periodic router tori, in ordinary and final optimized execution. Additional stress: all 36 single-FORK-box cases formed by six ordered distinct-port pairs and six displacements, namely (0,0) and (k,1) for k=-2,...,2. Each used the complete torus at the minimum B=96, testing degree, co-degree, ownership and induced routes rather than a clipped patch.
- Final optimized coefficient suite: 336,672 support/halo queries, 500 signed period shifts, 4,698 fixed primitive-plane points, 16 pair-loader cases, 9,216 prism integer cases and eight rejected malformed/tampered cases. Inspected explicit exception guards; no optimization-disabled assertions remain in the reviewed Python.
- Worked example independently replayed: 43 seeds, U15 halt at T=75 and p=-13, CA extinction at H=184, 18,257 active CA cells and the stated physical prism. Its receipt hash is included below. No full sandpile execution is asserted.

## Resolved corrections

1. Replaced the stale 3B route-length receipt by the current proved 4B bound and regenerated its support bound.
2. Corrected the false blanket assertion that distinct shafts always have different x coordinates: same-port copies in different time rows have equal x and y separation at least B. The other clearance arguments already handle this case.
3. Corrected the main proof's stale CA-proof filename and clarified least-closure/fair-history terminology.
4. During conversion of assertions to explicit exceptions, caught an insertion between @dataclass and class Edge that made imports fail. The decorator placement was fixed and the final modules rerun successfully.
5. Final primitive receipts use the actual tail length 12. The directly checked longer/shorter tail variants are supplemental evidence only.

## Boundary of the verdict

The infinite-support conclusion rests on the reviewed general coordinate and least-closure proofs. The approximately 1.9e27-entry dense period and a full universal-circuit sandpile run were not materialized. Arbitrary-program-to-U15 encoding remains the separately named Neary-Woods dependency. This audit does not supply an odometer/Diophantine certificate composition or an immutable release gate. verify_bundle.py is correctly described as a receipt-regenerating research replay runner. The final aggregate VALIDATION.json reports six normal/optimized replay successes. Independently verified that all six recorded receipt hashes match the actual files and all 24 byte lengths and hashes in FROZEN-INPUTS.json match the frozen package. This integrity check is distinct from executing an immutable release wrapper.

## Exact SHA256 snapshot

- `README.md`: `31827d25a5a96daca4e7a921c40188c94c7330518cb9808b1b38f4868102d5c5`
- `LOADER-PROOF.md`: `1791518f521a147b014ca7636910b7775df64fcfe799b6fcb5a0261de4f99d34`
- `PROVENANCE.json`: `340b750ddc359f8f143aa0a433332f93dacb2790d484efb676f59e95a40067c1`
- `verify_bundle.py`: `9c05134e2856e1bea3231227edfd75b0cabce01c58fe367ebf83a91f5610f582`
- `data/u15_table.json`: `0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a`
- `gates/GATE-PROOF.md`: `22aba118cac6b374f3adbc10b0ff8cd02cd03c3d8d7b78ffb9ec158e42165d11`
- `gates/check_gates.py`: `44ffb9fe7f16d81304737c94fa53744ac053c2e6e32b29909a211cf960c2fa21`
- `gates/gate_receipt.json`: `e20a2dd8401b863ce31787ea1db225c423c75a4f6b799b0ca030c50b4a204f0e`
- `geometry/periodic_router_proof.md`: `e3ae994d51aa83eb58740cd4255e686e866bc668f7245908940e5f7f1bd41635`
- `geometry/periodic_router.py`: `7664316f71c5504a4cab8971368f6d7887bef1060f1425759d06b074dc509e95`
- `geometry/router_checks.json`: `498d33f9dde661e6ee7abcb96e73ff588baa866fe7fee5af34a0fbfc14b29d48`
- `ca/SEMANTICS_AND_BOUNDS.md`: `d1d4548303b91b484cc089fdb18fcae13721d1b24c1b820017557be7d755d358`
- `ca/lazy_u15.py`: `c279e5046806e034bd0cd65a101a7a2c5c312906d7001206fd3eb5928ca93907`
- `ca/test_lazy_u15.py`: `0732e3722ed28a26aa927f8786c10a4227e116f8843d9a7c73f340b44e520f37`
- `ca/manifest.json`: `8ee002769edbb3581c3e0758c5e6a121b92acdabbbb2f31391e07403c220c11c`
- `ca/rules.jsonl.gz`: `cc3752c9bcfa3e8b32d5dc41280a84e11f4c9453e824a44f9e8cff8efc8926e9`
- `ca/verification.json`: `a8419ad44cbf0ca803bd367dd9dc2b3d234e92c6f5ca68d1eaf4d09a63b3496b`
- `compiler/literal_loader.py`: `f879d4a285c749e493e7004f3e985779c425222ec5cbd165c93ac1601da7735a`
- `compiler/test_coefficients.py`: `1112b920d6f072ebe1406075b6ab26528c17757585aa8dec14d83ab26e59dc90`
- `compiler/make_example.py`: `1f7c1285a355080712c3c3f0c3a8e33eb751926cc2b0d761374307c111610304`
- `compiler/circuit_manifest.json`: `07c8d0ada8d953cc4287801349de29c990a21803c0081e077b7df1ffb3bc89ca`
- `compiler/coefficient_checks.json`: `400b16f76cd45fc9cb7f407672c2ed8db0bbe52cff1ccb1e4c297f38db3ba10a`
- `compiler/worked_example.json`: `c05ca48ac62450748e192adeec546866159f34115ad0d37ccc7c8c2808107ad1`
- `VALIDATION.json`: `a7de43a3182ec7dbc5223e353f809e777cf4901253b71287c43a13adcd133e13`
- `FROZEN-INPUTS.json`: `de3e161de813afb098110223f9850c49cb8bcd481af69f8b9789daa3ca2950e3`
