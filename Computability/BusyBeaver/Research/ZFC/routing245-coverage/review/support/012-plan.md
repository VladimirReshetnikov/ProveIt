# Routing245 v4 final coverage and endpoint closeout

Status: source-only plan, pending the actual terminal final batch. This is not a complete-evidence receipt. The accompanying `closeout-inventory.json` fixes the source family, ten terminal prior batches, three historical failures and known endpoint parents. It deliberately leaves the final batch and Sites record hashes null. No supplied generator, guard, builder or proof compiler was executed for this plan.

## Exact expected census

The frozen v4 manifest is `v4/sources/generation.json`, SHA `b79fe539f343ca2f8979ada70f534f2ee08fb2361598a87f39c1e410fe6c32bc`. The executed v4 guard is `check-production-v4.py`, SHA `c37473de1eacb7a47a397e49bbff9b0bed9eeb1efbebea21f3c0835ecf42f7b5`.

| Category | Modules | Probes | Callers |
|---|---:|---:|---:|
| v4 generated family, indices 0–598 | 599 | 905 | 905 |
| Exact earlier successful modules | 25 | 53 | 56 |
| Complete selected proof family | 624 | 958 | 961 |

The 25 reused modules are exactly three subtree pilots, thirteen original production batches, v2 Cut043, and eight v3 successes. Ten terminal v4 batches cover indices 0–291 without gaps. `final307-run1` selects 292–598. Only after its `batch.json` is terminal `PASS_COMPLETE_COVERAGE`, with all 307 selected records and its complete census, may the final batch become the complete aggregate. An additional invented aggregate is unnecessary: the existing builder recursively follows its ten exact `prior_batches` references. Preserve the terminal aggregate bytes and hash, rather than reconstructing its status.

The final unit is `BusyBeaver.ZFC.SitesRouting245`, index 598, with source `3527da1cffbeb701b01ea8c1a79bd3c5767ca08c5ced2fbc87cc7cd6605ca896` and audit `d9319cd2718bc2a2c175f43c100ad42433396025f81966229339a687fa6125ca`. Its three probes/callers establish `all_sites`, checked actual-program walks, and existence of the actual-program walk for every pointer. The tree has 6,460 leaves, 8,391 guards and decoder depth 51. New closed checks use at most 32 guards; historical larger blocks remain selected only through their exact actual PASS records.

## Complete existing-evidence review

Use one family receipt, not 624 independent paperwork packets. The receipt schema in `complete-review.schema.json` is the exact minimum consumed by the preserved builder, with stronger count constraints for this family. The reviewer must disclose source/guard authorship, if any. It is an existing-evidence review with no proof replay.

1. Read the final source/audit and verify the complete join graph from the frozen manifest. Every join must require both actual children, and every selected module except the final theorem must be an ancestor used by the final object. Keep the original source-family reviews as supporting evidence; they do not replace the actual record checks.
2. Build a unique index of the 599 new modules from the final batch and recursively pinned prior batches; then insert the manifest's exact 25 reused records. Reject missing modules, duplicate modules with different record identities, prepared records, live records, failed records and unexplained warnings. Require exactly 624 selected `(module, absolute record path, record hash)` entries.
3. For each selected record, require source then audit success, actual raw log equality, default proof limits, `-j1 -M4096`, shared 120 seconds, fixed fuel 4000 and margin 64, no dependency build/download/version query, and the declared per-unit probe/caller census. Parse the named axiom reports in the exact audit order and permit only the standard three axioms. Require all selected warnings zero. Sum actual reports/callers to 958/961; do not substitute the manifest census for parsing the actual outputs.
4. Verify every source/audit and snapshot hash, all before/after identities and selected actual first providers, complete imported-source DFS and current source/object pairs. Deduplicate filesystem hashing by `(absolute path, expected hash)` for efficiency, but reject conflicting hashes before caching; compare every record reference and rehash each unique current input once again at review close.
5. Require one actual fresh object per unit, matching the source hash, saved immediately after source and before audit, selected as first provider then, and unchanged after audit. Compare all shared fields rather than whole metadata dictionaries: source capture includes `source_command_index`, and first-provider field names may differ.
6. Every non-pilot selected proof has its exact successful `preparation` record: unbuilt, empty commands/fresh modules, same source/audit/manifest/provider bindings and before/after equality. Only the three explicitly pinned historical pilot records have the older no-separate-preparation schema. Do not manufacture such records for them.
7. The final Sites actual record must have 646 project providers, plus Init/Omega. Verify every one of the other 623 selected coverage modules occurs there with precisely its selected source and fresh object hashes. Its remaining 23 projects are the generic base. Recompute this closure, rather than trusting a stored count alone.
8. Preserve the v1 unit013 timeout, v2 cut42 recursion failure and v3 cut49 recursion failure, with exact source/audit snapshots, logs, original statuses and rejected/abandoned versions. The inventory pins all three failures. A failed unit never becomes a provider. The old reviews retain their source-only or partial-run scope.

The final receipt must set `status` to `CLEAN_COMPLETE_ROUTING245_COVERAGE_EXISTING_EVIDENCE_REVIEW` only after those checks pass. It must enumerate all 624 exact selected records, bind the actual final record (not the batch summary), give `final_projects=646`, and set all three current-input/provider/pre-audit flags true. Include a compact detail report, reviewer source script and relevant immutable family/history reviews in `supporting_artifacts`; the builder explicitly maps these even if outside its history roots. A plan, root count summary, or running batch is not that receipt.

## Publication using the existing builder

The preserved 268-line builder is `publication-design/build_packet.py`, SHA `b76debc93bfbf032ca3c2d9b3f8bd1fa160370e5a9c9495b564e797728557ed1`, independently source-reviewed in `independent-dynamic-builder-review.json`. No body change is currently needed. Root runs it only after exact terminal aggregate and independent receipt hashes exist:

```sh
python3 -B /tmp/zfc-routing245-lean/coverage-production/publication-design/build_packet.py \
  --manifest /tmp/zfc-routing245-lean/coverage-production/v4/sources/generation.json \
  --manifest-sha b79fe539f343ca2f8979ada70f534f2ee08fb2361598a87f39c1e410fe6c32bc \
  --guard /tmp/zfc-routing245-lean/coverage-production/v4/check-production-v4.py \
  --guard-sha c37473de1eacb7a47a397e49bbff9b0bed9eeb1efbebea21f3c0835ecf42f7b5 \
  --complete-batch /tmp/zfc-routing245-lean/coverage-production/v4/final307-run1/batch.json \
  --complete-batch-sha ACTUAL_TERMINAL_BATCH_SHA \
  --complete-review /absolute/path/to/complete-review.json \
  --complete-review-sha ACTUAL_INDEPENDENT_RECEIPT_SHA \
  --output /tmp/zfc-routing245-complete-coverage-publication
```

`ACTUAL_*` are deliberately unresolved placeholders. The builder stages 621 selected sources plus three already-maintained pilot prerequisites; all 624 audits, raw records and two logs per unit; final record alias `results/routing245-coverage-verification.json`; all versioned source-generation metadata and scripts; complete review/support registry; and `results/routing245-coverage-publication.json`. History is `routing245-coverage/history.json` with standalone content-addressed blobs and original absolute-path aliases. Existing identical maintained files are allowed; differing bytes fail closed. Root must independently rehash every map entry and history alias roundtrip before installation.

The original execution guards and generators remain provenance, with historical cache prerequisites. No new portable guard framework or clean-checkout cache claim is introduced. Compiled objects and cache symlinks remain excluded and hashed as exclusions.

Size risks: 624 records contain substantial repeated input/provider lists; many captured history directories are mirrors of earlier versions. Keep exact record JSON files once by content hash, not nested into a new JSON array of full records. Use references in the complete receipt/detail report. The existing builder deduplicates all history bytes against already-mapped source/audit/record/log bytes and across mirrored histories; do not replace this with another monolithic `text_by_sha256` JSON. Necessary unique proof records still consume space. Report both `unique_history_bytes` and `history_alias_bytes`, plus compiled exclusion count; do not use object-cache bytes as publication size. Map/support registries preserve any relocated deduplicated destination.

## Endpoint successor guard: freeze only after actual final Sites PASS

The endpoint source and audit are unchanged: `BinaryRouting245.lean` SHA `4750d624a4272c5209b3af467143e91ee9eddea3adf7f8aa707d49435e7d80eb`, audit SHA `0c1eb14a9efe8f0438beddaf060b9df9d247c8a586115e06c3352b8017e36c71`, eleven probes/callers. Its four direct imports are RuntimeInstanceRouting245, BootstrapFrameRouting245, SitesRouting245 and BisimRouting245.

Known immediate actual parents:

- Runtime run1: `9371377fd870cc2c093591effa3891feb99d7ba0f3a42e566d703c3d67f03835`, 11/12.
- BootstrapFrame run1: `9b11432d5751e781a53639bd427be219055ed3615d5f88e038d36a177f3d6997`, 8/9; the selected padding-nine source is the checked one.
- Full source bisimulation final-run1: `a2093e5c80fd41dbfff2d59931319b4c971967b50166ae0838166086b982349b`, 5/6.
- Sites index598: actual record hash remains pending, expected 3/3.

The old `endpoint/check-pending.py` remains immutable historical evidence: its 330-project list describes the superseded coverage layout. The independently recomputed prospective endpoint DFS is **851 projects**, with Init/Omega. The change is 592 added names and 71 removed names, not merely a net-count append. The complete exact prospective source list is in `closeout-inventory.json`. It contains no invented future object hashes.

After final evidence review, create a separate successor guard by retaining the original execution body and source/audit pins, binding BootstrapFrame and Sites to their actual records and replacing the entire `expected_modules` list with the newly derived 851-name list. Recompute this list from the union of the four actual parent records' selected source/object pairs plus each fresh module, not just from the static plan. Conflicting duplicate module bytes fail closed. Check the two derivations agree exactly; every future source/object identity comes from a real PASS. Preserve the old pending guard, its source-only inventory and this plan before writing the successor; record a focused CFG-only diff and an explicit parent-freeze receipt. Root reviews the full delta/body, then performs a fresh prepare-only run and normal source+audit run under the same 120-second/default limits. No endpoint proof attempt is authorized by this plan's prospective census alone.

The endpoint is an external Lean equivalence for the literal 245-state, two-symbol machine starting at state zero, head zero and empty tape. It combines exact 407,915-step startup, whole-tree runtime coverage, arbitrary-register source bisimulation and the calibrated logical seed. Its eventual nonhalting/ZF–ZFC consistency theorem is not an internal PA proof and not an unconditional nonhalting or consistency assertion. Coverage publication and endpoint publication stay separate evidence units.
