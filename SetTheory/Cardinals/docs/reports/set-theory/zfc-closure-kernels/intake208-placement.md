# Batch 208 placement: Sources 176–178

Arrival `aa66d0a33f1f8237a348899eb8095b045a502832` adds three proof-research archives, numbered alphabetically here. They continue the existing `zfc-closure-kernels` report; they add no report directory and do not alter its base article. This placement preserves submitted material before the separate written reconciliation and any proof integration.

| Source | Original archive | Members | Expanded bytes |
|---|---|---:|---:|
| 176 | `Affine_Proof_Cores_and_Transport_2026-10-21.zip` | 105 | 8,143,711 |
| 177 | `K215_Certificate_Refinements_2026-10-21.zip` | 106 | 1,073,294 |
| 178 | `K215_Checked_Simplifications_2026-10-21.zip` | 194 | 2,752,810 |

The [exact member map](data/intake208-placement.json) records all 405 original names, sizes and byte identities. There are 140 immutable Git references, 247 occurrences backed by 245 new ancillary files (3,934,908 bytes), and 18 main manuscript/README/TeX/PDF members recovered from the arrival ZIPs under the reconciliation-note exception. The 247 placed occurrences include two exact aliases of earlier new files. Alias selection uses immutable `d1b55dde4598f06cfb1814d0b403d2ab5ceba49b` paths and two older arrival paths, never an unpinned future working tree. Original notices, licenses, raw proof logs, unsuccessful-search records, scripts and manifests are retained unchanged. A file being new to this placement does not establish mathematical novelty.

Source 176 embeds the exact original Source 168 and revised Source 174 archives. Their 165 and 360 members are separately recorded in the [nested inventory](data/intake208-nested-inventory.json) and remain recoverable from their historical Git arrivals; neither ZIP is copied again. Nested members are not added to the 405 outer-member count. All archives have unique regular-member names and no unsafe paths, symlinks or compiled objects.

The code/data subdirectories use short numbered filenames. The map retains each delivered directory layout and its exact recovery route; it does not rewrite source imports or make flattened scripts runnable in place. Main-document recovery does not depend on a rewritten article. No supplied program, compiler, checksum suite or TeX build was run in preparing this placement.

The new [streaming recovery helper](code/intake208-recover.py) independently recovers every outer member, compares it directly to the arrival ZIP bytes, and checks both nested inventories without creating an output tree. Its [actual control](data/intake208-recovery-control.json) passes all 405 members and the nested 165/360 members. [Changed-hash and omitted-member controls](data/intake208-negative-controls.json) both fail as intended. The [Git-filter control](data/intake208-filter-control.json) confirms every new payload's clean-filter blob equals its original blob; no scoped raw-text attributes were needed. These are recovery checks, not certification of delivered mathematical results.

## Review boundaries and intended follow-up

Source 176 develops relative affine/run transport and raw-code axiom transport, plus graph-origin certificate ideas. Source 177 supplies a balanced certificate-storage refinement, three marker-fold instances and a concrete Cantor-code prefix-credit proof. Source 178 supplies a Lean framed decoder certificate and a normalized source-certificate variant, with finite search negatives. Their main pin is the older `53269bcab1` snapshot. The new material must be reconciled with the completed phase-five K215 endpoint and the already received normalized-checker proposals. Submitted compilation receipts retain their own toolchains and scopes; the placement itself promotes no new endpoint, machine or performance claim.

The maintained proof sources, catalogue and current formal-status notes are untouched by this placement. Sources 165/166 remain pending written follow-up. The three arrival ZIPs are retired in this placement commit after independent recovery review. Historical evidence and all other incoming files are outside this change.

## Recovery

From the repository root:

```sh
python3 SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake208-recover.py --verify-only
```

Use `--result /new/path.json` for a fresh receipt; existing receipts are rejected rather than overwritten. The helper requires only Python's standard library and access to the recorded Git history. It does not execute any recovered file.
