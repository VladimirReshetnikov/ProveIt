# Exact246 decoder coverage

This packet contains the complete 102-module coverage proof for the canonical
contextual-fold246 machine, with 468 named axiom probes and 468 typed callers.
The frozen decoder has 6,460 leaves and 8,391 guarded cases. Its 233 closed cuts
are combined by 232 joins, each requiring proofs for both children.

The final theorem is
`SetTheory.BusyBeaver.ZFC.SitesPrefix246.all_sites`.
`actual_walk_checked` and `actual_walk_exists` apply to every finite PC list,
including the decoder's zero-padding behavior. The checked site-execution
soundness is imported explicitly. The separate `BinaryPrefix246` theorem
combines this coverage with runtime simulation, the complete 410,735-step blank
bootstrap and logical calibration. This coverage packet alone does not assert
an internal PA consistency equivalence or unconditional nonhalting.

Read the [publication manifest](coverage-prefix246/manifest.json) and the
[exact final proof record](results/prefix246-sites-verification.json). The
manifest retains every selected source/audit record, exact planned and executed
guards, logs, failures or interrupted history, and the complete existing-evidence
review. Three representative cuts were executed with earlier equivalent-source
guards; both guard identities are retained. The original coordinator interruption
and its recovery are preserved without rewriting the stale RUNNING summary into
a success. Later complete proof evidence supplies the publication gate.

Every new source/audit pair used default proof limits, one thread, 4,096 MiB and
a shared 120-second budget. Historical imported modules and the exact cached
parents are explicit boundaries; they were not rebuilt under these defaults.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted by the audits.
Observed warnings remain in the original records.

The source generator and its exact grouping are reproducible with:

```
python3 -B coverage-prefix246/programs/generate_sites_prefix246.py \
  --repo REPO --output NEW_PLAN --max-guards 64 --joins-per-module 16 \
  --cuts-per-module 4 --max-batch-guards 128
```

The portable guard generator is next to its exact bundled template. Its sole
change from the preserved original is the template lookup path. The installed
coordinator stages a separate execution manifest and guard variants whose only
changes are default source/audit paths; the raw historical manifest is unchanged.

From this directory, supply the SHA-256 of the reviewed published manifest:

```
python3 -B check_prefix246_sites.py --repo REPO --manifest-sha MANIFEST_SHA \
  --output NEW_STAGE --stage-only
python3 -B check_prefix246_sites.py --repo REPO --manifest-sha MANIFEST_SHA \
  --output NEW_PREPARATION --prepare-only --wall-seconds 1400
```

Staging invokes no child programs. Preparation performs 102 Python guard
preparations using exact historical successful predecessors. Each leaf has
`commands=[]`, `fresh_modules=[]` and no compiler/version query. The coordinator
therefore records 102 Python commands; preparation is not a proof replay.
Its record and independent review are separate results files outside the frozen
publication manifest.

For a new proof replay, omit both preparation flags. The default is a bounded
10-unit session; `--max-units` and `--wall-seconds` are explicit finite limits.
Subsequent sessions may pass a JSON list of validated prior proof-record paths
with `--reuse-list`. The unchanged serial runner uses newly produced predecessor
objects, stops on failure and retains every attempt. Only `PASS_COMPLETE_PLAN`
means every module, including the final theorem, has passed in the combined plan.
A partial budget stop is not the closed endpoint.

These commands require the exact compiler and imported project/cache objects
identified in the MP254 and Site246 parent records. Source publication does not
provide those binary caches. Missing or changed prerequisites require a separate
reviewed rebuild/pinning workflow; old raw records are never rewritten to claim
that a new cache is the historical one. The archived packet builder packages
existing evidence only and is not a dependency builder.
