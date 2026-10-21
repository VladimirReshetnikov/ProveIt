# Batch 212 placement: checked affine core and CM215

This placement accounts for one manuscript from arrival `6f0d42d368506bc29c70ace1c992ed88b2651346`, `K215_Checked_Affine_Core_and_CM215_2026-10-21.zip`. It is **Source 179**, an addition to the existing ZFC closure-kernels report, using the prefix `179-affinecm-`. The highest existing numbered source was 178; this continues that local sequence and creates no new report. The separate earlier batch-209–211 reconciliations and Sources 165–166 follow-ups remain pending.

The manuscript continues the existing affine-source, semantic-proof and alternative-machine work. It is pinned to `56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3`. Its recorded Coq/Lean checks are delivered evidence, not fresh intake executions. The currently checked, shorter K215 proof and its exact machine are not overwritten. The written mathematical reconciliation and catalogue update follow this placement commit.

The [exact member map](data/intake212-placement.json) covers all **862 files / 11,367,916 expanded bytes**:

| Recovery route | Members |
|---|---:|
| Exact immutable Git aliases | 462 |
| New ancillary payload files | 338 |
| Repeated new delivery members | 24 |
| Main README, manuscript/includes and PDF retained in arrival ZIP | 6 |
| Raw logs excluded by existing Git ignore rules, retained in arrival ZIP | 32 |
| Total | 862 |

The 462 Git aliases comprise 460 members present exactly in tree `e4171548f9d70b23ef8112b02c5683e23ec628a7` and two available at the delivery pin. All member blob IDs were also compared with reachable Git history; no additional history-only matches were found. The chosen immutable aliases were compared directly with fresh arrival bytes. The [overlap summary](data/intake212-history-overlap.json) and [complete inventory](data/intake212-inventory.json) preserve this boundary.

The 338 new files occupy 6,339,936 bytes. Scripts, proof sources and patches are under `code/`; records, certificates, licenses and table data are under `data/`; new provenance/component markdown is at this report root. All use short ordinal filenames under the source prefix; the member map records every original path. Maximum repository path length including `C:/ProveIt/` is 139 characters. Delivered source text, historical status statements, failed attempts and instructions remain unchanged. Relative delivery paths inside those files refer to the reconstructed layout, not these shortened placement names.

The archive's six manuscript members and 32 ignored raw logs (63,618 bytes) remain recoverable from its committed arrival. The existing Git ignore rules apply to delivery logs under incoming procedure sections 1 and 3; these logs are not force-added. Their exact member names, byte counts and digests remain in the recovery map, including failed-run logs. Existing payloads and repeated new members are referenced rather than copied again. In particular, the older 188-file Lean snapshot is accounted for without replacing maintained Lean files. The exit-137 certificate attempt, failed CM215 audit client and rejected 214-state experiments remain in the recovery map. Attribution and inherited license notices are preserved.

The [own recovery helper](code/intake212-recover.py) treats all payloads as inert data. It reconstructs or verifies every member against the original Git ZIP, without invoking a submitted checker, compiler or checksum manifest:

```sh
python3 SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake212-recover.py --verify-only
# Optional fresh reconstruction for later source review:
python3 SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake212-recover.py --out /tmp/k215-affinecm-reconstructed
```

The [positive recovery control](data/intake212-recovery-control.json) verifies all 862 exact members. The [negative controls](data/intake212-negative-controls.json) reject a changed member digest and an omitted map member. These are intake-accounting controls, not mathematical verification. No submitted program, proof compiler or PDF build was run for placement; no line endings or checksum manifests were normalized or validated.

Only the single arrival ZIP named above is retired in this placement commit, after the member accounting is reviewed. The incoming README remains in place. The archive is permanently recoverable by `git show 6f0d42d368506bc29c70ace1c992ed88b2651346:docs/incoming/K215_Checked_Affine_Core_and_CM215_2026-10-21.zip`.
