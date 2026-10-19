# Provenance and attribution

## Pinned logical and machine baseline

- Repository: <https://github.com/elliotglazer/k230-rocq>
- Revision: `3142e4dd980f0be12f4abb636c4ae2528afc17eb`
- Author of K and the released K230 calibration: Elliot Glazer.
- Exact table: `inputs/k230.tm`, SHA-256 `e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8`.
- Exact source certificate: `inputs/sites230.json`, SHA-256 `400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487`.
- Endpoint: `coq/tm/Correct230.v`, `tm230_halts_iff_ZFC_inconsistent` and `tm230_nonhalting_iff_ZFC_consistent`.
- The unchanged pinned local repository, including original notices and source line endings, is preserved in `provenance/k230-rocq-3142e4dd.zip` using `git archive`. It does not include the external Jeff reference checkout, generated proof objects or Git history.
- The upstream reference revision is `c132d7eae8158cd3a9850ea3eb7251158c3dd821` of <https://github.com/jeff87654/busy-beaver>.

The preserved K230 README, third-party attribution, manifest and provenance JSON are authoritative for its recorded Rocq builds and license scope. The source audit in `evidence/k230_source_audit.json` is a read-only hash/declaration/lexical audit of 103 manifested local files. It is not a fresh compiler or kernel run. Its reproduction script is retained under `provenance/` and accepts `--repo` pointing to a Git checkout of the pinned revision.

## Previous ProveIt reductions

- Repository: <https://github.com/VladimirReshetnikov/ProveIt>
- Comparison commit: `0128d662fd46f72dc84505176ae8ec28affb2d9d`.
- Original research archive: `docs/incoming/ZFC235_Construction_2026-10-19.zip`.
- Source-loop rotation and the two fold ideas used here were developed in the preceding 243-to-235 reduction chain. Their mapping to K230 is recorded in `provenance/transfer-accounting.md` and the report.
- `code/verify_state_fold.py` is preserved from that 235-state package's `verification/verify_state_fold.py`.
- The primary symbolic runtime inference engine and PC helpers derive from the previous ProveIt mathematical verification. The earlier research's generic runtime engine was supplied through the 236/237 research package lineage. The four block traversal entry labels, dispatcher and halt label were adapted to K230; unused legacy command-line code was removed in the primary package. The mathematical inference rules were retained, and both complete K230 and K228 runtime certificates were then recomputed on these exact packaged files. `code/source_semantics.py` retains the original PC operations and register permutation.
- The local fold wrapper only renames the separate halt 230 to 254 for the unchanged inherited checker; it does not change working-state semantics.

## Contributions made in this investigation

ChatGPT prepared this research for Vladimir Reshetnikov and the ProveIt project on 19 October 2026. New work consists of the exact old-to-K correspondence audit, transfer and composition of the two reductions, standalone deterministic construction, canonical table, exact initialization checks, complete final runtime proof, independent source/frame composition audit, report, and the optional shared-decoder alternative with its proof and search records.

The archived independent audit notes and original builder validation retain the hashes from their own historical research stage. The release's authoritative primary execution receipts are the files under `evidence/`, whose hashes refer to the final code under `code/`. The original builder is retained under `provenance/original-build_k228.py` so that its recorded historical hash remains reviewable. The primary builder differs only in packaging/CLI integration; the exact generated machine, source and construction receipt are unchanged.

The optional alternative-layout supplement preserves its own supported runtime driver and exact checker snapshots so its previously generated evidence remains reproducible. Its unused legacy entry points are not the commands documented in that supplement.

## Attribution and license scope

The machine and verification lineage includes Mira, Vladimir Reshetnikov's ProveIt project, Jeff's busy-beaver reference, Elliot Glazer's compact K theory and proof, and Andrew James Wade's Turing Machine Explorer/compiler. Existing ProveIt and Wade notices are preserved in `licenses/`; K230's complete `THIRD_PARTY.md` and `LICENSES/` are preserved in the upstream source archive. K230 explicitly does not assert a blanket license for custom or adapted source portions whose licensing was unspecified at the pinned upstream source. This package does not relabel those portions with a new license.

The ordinary K228 proof inherits the particular mathematical calibration of the pinned machine. It does not claim a fresh Rocq build, a fully encoded internal ZFC/PA derivation, or a proof of consistency of ZFC itself.
