The exact246 coverage lane uses the same complete decoder tree and 233-cut frontier as the reviewed250 plan. Every cut is a closed kernel decision about `allSites SitePrefix246.checkSite` on `descend ActualTree254.tree`; all 232 structural joins require both actual child subtrees. No delivered Python result or external coverage list is a logical premise.

Three isolated representatives are ready in `representatives/`: cut0 has10 leaves/13 guard cases and path length1; cut42 has47 leaves/61 guards and path length23; cut210 has26 leaves/34 guards and path length24. Their source and audit bytes remain identical in every generated full grouping. Their standalone guards pin the exact source/audit and24 project prerequisites, plus supplied Init/Omega; the Site246 PASS pin must be frozen before use. Root exclusively runs them. No representative theorem has been proved by the source-generation work.

`generate_sites_prefix246.py` supports at most16 cuts and512 guards per source file, with the representatives kept separate so their successful objects can be reused. File grouping does not alter any proposition. With the fixed frontier and16 joins per composition file, static grouping counts are:

| Maximum cuts / guards per file | Cut files | All files |
|---|---:|---:|
| 1 /64 |233|249|
| 4 /128 |86|102|
| 8 /256 |40|56|
|16 /512 |21|37|

These are file counts, not runtime predictions. The root should select a grouping after actual pilot/heavy/deep timings, preserve those records, and use a fresh output for the selected generated plan. Grouping savings are slightly lower than the earlier250 estimate because all three representatives are isolated here.

The final audit is complete from generation: it probes and calls `all_sites`, `actual_walk_checked` with its typed actual-`Prog254.program` walk hypothesis, and `actual_walk_exists` for arbitrary PCs. There is no deferred final-audit expansion. The generic `SiteCoverage` clients use the checked `ActualTree254.tree_eq` bridge. The all-sites theorem establishes instruction coverage only; blank startup and the dirty logical source bridge remain separate.

`prepare_plan_guards.py` emits a separate frozen guard for each generated source/audit unit. Each joins only its required direct generated dependencies, requiring exact successful records, source and audit hashes, fresh objects recorded before audit, and exact current source/object providers. The expected transitive import closure is24 generic/site providers plus the precise imported generated modules. Pending Site pins are deliberately non-executable. Preparing guard text invokes no guard, compiler or version query.

`run_pipeline.py` is a root-run serial orchestrator. It accepts a reviewed manifest and explicit manifest hash, validates every source/audit/guard byte, and verifies any reused successful records against the selected plan and all their current input-provider hashes. It never builds dependencies implicitly. Each guard compiles only its named source then its focused audit, with default proof limits, `-j1 -M4096`, and a shared120-second bound. The runner also has explicit new-unit and total-wall bounds. It stops at the first failure or evidence mismatch, preserves the attempt, and kills the whole process group if its total wall bound expires. A three-second termination grace is recorded. `--prepare-only` validates and records readiness without invoking any guard or compiler.

A bounded continuation uses a fresh runner output and a JSON list of prior successful record paths through `--reuse-list`. The runner does not delete or alter prior attempts. Reused representatives must match the unchanged isolated module bytes. `PASS_COMPLETE_PLAN` is available only after every selected full-plan unit, including the three-client final module, has a valid record. Selected representatives alone cannot claim the endpoint.

Example source preparation, after the actual Site246 PASS exists:

```sh
python3 -B /tmp/zfc-prefix246-lean/coverage/prepare_representative_guards.py \
  --site-evidence /tmp/zfc-prefix246-lean/site/run1/verification.json
```

Root runs each resulting `check-cutNNN.py` with `--repo`, that exact `--site-evidence`, and a new `--output`. After measuring them, generate a chosen grouping (the following numbers illustrate an option, not an approved runtime choice):

```sh
python3 -B /tmp/zfc-prefix246-lean/coverage/generate_sites_prefix246.py \
  --repo "$PWD" --output /tmp/prefix246-coverage-selected-plan \
  --cuts-per-module 8 --max-batch-guards 256
python3 -B /tmp/zfc-prefix246-lean/coverage/prepare_plan_guards.py \
  --plan /tmp/prefix246-coverage-selected-plan \
  --output /tmp/prefix246-coverage-selected-guards \
  --site-evidence /tmp/zfc-prefix246-lean/site/run1/verification.json
```

The root reviews the resulting manifest and its printed SHA before invoking the runner. A typical bounded first preparation passes `--max-units 1 --wall-seconds 180 --prepare-only`; removing only `--prepare-only` requests the actual source/audit run. This source-only task has not invoked either mode of the runner or any generated guard.

If a batch hits a wall/memory bound, reduce its file grouping and preserve the failed record. If a single cut hits Lean's default per-declaration limit, split that actual subtree and introduce both-child composition rather than increase limits. A failure at one actual leaf requires proof-producing computation decomposition; neither grouping nor a Python success report proves that leaf. Existing imported objects retain their historical proof options; this workflow reuses them explicitly and does not claim to rebuild them under these new limits.
