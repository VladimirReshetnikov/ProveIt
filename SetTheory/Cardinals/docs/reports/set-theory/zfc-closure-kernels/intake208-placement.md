# Batch 208 supplemental placement: Sources 176–178

Arrival `aa66d0a33f1f8237a348899eb8095b045a502832` adds three proof-research archives, numbered alphabetically here. They continue the existing `zfc-closure-kernels` report; they add no report directory and do not alter its base article. Upstream `8e3066c70b` and our parallel commits `df67839df1`/`aecdc78a8b01aae7d03b055cb6ef944f8b9b45c0` placed the same arrivals. This supplement reconciles their exact bytes and recovery routes without renumbering the sources or treating them as another batch. Separate written reconciliation and proof integration retain their own evidence.

| Source | Original archive | Members | Expanded bytes |
|---|---|---:|---:|
| 176 | `Affine_Proof_Cores_and_Transport_2026-10-21.zip` | 105 | 8,143,711 |
| 177 | `K215_Certificate_Refinements_2026-10-21.zip` | 106 | 1,073,294 |
| 178 | `K215_Checked_Simplifications_2026-10-21.zip` | 194 | 2,752,810 |

The [exact member map](data/intake208-placement.json) records all 405 original names, sizes and byte identities. The current map uses 348 immutable Git references, 39 exact ancillary files (39,707 bytes) omitted by the upstream placement, and 18 main manuscript/README/TeX/PDF members recovered from the arrival ZIPs under the reconciliation-note exception. The retained ancillaries are 37 raw logs and two checksum records, preserved as data rather than executed or verified manifests. Git aliases bind the upstream `8e3066c70b` tree, earlier `d1b55dde4598f06cfb1814d0b403d2ab5ceba49b` paths and two historical arrival paths, never an unpinned future working tree. Original notices, licenses, raw proof logs, unsuccessful-search records, scripts and manifests remain recoverable unchanged. A new placement does not establish mathematical novelty.

Source 176 embeds the exact original Source 168 and revised Source 174 archives. Their 165 and 360 members are separately recorded in the [nested inventory](data/intake208-nested-inventory.json) and remain recoverable from historical Git arrivals; neither ZIP is copied again. Nested members are not added to the 405 outer-member count. All archives have unique regular-member names and no unsafe paths, symlinks or compiled objects.

The first parallel placement used 245 unique ancillary files, 140 Git references, two intra-batch aliases and 18 arrival fallbacks. Its original map/helper/controls remain exactly recoverable at `aecdc78a8b01aae7d03b055cb6ef944f8b9b45c0`; the earlier incomplete `df67839df1` commit is retained rather than silently replaced. After comparing all 206 duplicate files against immutable upstream bytes and passing a complete recovery control, this supplement removes only those 206 files from our numbered raw directories. The [deduplication record](data/intake208-deduplication-control.json) identifies every original and replacement path. No upstream asset is removed.

The original code/data subdirectories used short numbered filenames. The map preserves each delivered directory layout and its exact recovery route; it does not rewrite source imports or make flattened scripts runnable in place. Main-document recovery does not depend on a rewritten article. No supplied program, compiler, checksum suite or TeX build was run in preparing this placement.

The new [streaming recovery helper](code/intake208-recover.py) independently recovers every outer member, compares it directly to arrival ZIP bytes, and checks both nested inventories without creating an output tree. Complete controls pass both [before](data/intake208-recovery-v2-before-removal.json) and [after](data/intake208-recovery-v2-after-removal.json) removing the duplicates: all 405 outer members and nested 165/360 members. [Successor changed-hash and omitted-member controls](data/intake208-negative-controls-v2.json) both fail as intended. The original [Git-filter control](data/intake208-filter-control.json) confirms all 245 first-placement payloads had clean-filter blobs equal to their originals; no scoped raw-text attributes were needed. Original recovery/control records remain historical; the successor map requires only the 39 retained raw files. These are recovery checks, not certification of delivered mathematical results.

## Review boundaries and intended follow-up

Source 176 develops relative affine/run transport and raw-code axiom transport, plus graph-origin certificate ideas. Source 177 supplies a balanced certificate-storage refinement, three marker-fold instances and a concrete Cantor-code prefix-credit proof. Source 178 supplies a Lean framed decoder certificate and a normalized source-certificate variant, with finite search negatives. Their main pin is the older `53269bcab1` snapshot. The material must be reconciled with the completed phase-five K215 endpoint and already received normalized-checker proposals. Submitted compilation receipts retain their own toolchains and scopes; placement promotes no new endpoint, machine or performance claim. In particular, maintained Lean already has balanced certificate-tree storage; this differs from the separate fast physical-table lookup proposal for site checks.

The maintained proof sources, catalogue and current formal-status notes are untouched by this supplement. Sources 165/166 remain pending written follow-up. The three arrival ZIPs are already retired by the parallel placement commits and remain recoverable in Git. Two later arrivals, `K215_Automatic_Certificates_2026-10-21.zip` and `K215_Proof_and_Quotient_Detachment_2026-10-21.zip`, remain pending and are outside this batch. Historical evidence and all other incoming files are outside this change.

## Recovery

From the repository root:

```sh
python3 SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake208-recover.py --verify-only
```

Use `--result /new/path.json` for a fresh receipt; existing receipts are rejected rather than overwritten. The helper requires only Python's standard library and access to recorded Git history. It does not execute any recovered file.
