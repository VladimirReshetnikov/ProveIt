# Complete exact246 coverage publication plan

This is a source-only publication plan. The release gate is the complete frozen
102-module plan and its final `SitesPrefix246` source/audit PASS. A partial runner
summary does not satisfy that gate. The current reviewed continuation starts from
34 successful modules; the remaining 68 are being run by root. This document
neither invokes a guard nor predicts their outcome.

## Fixed mathematical scope

The frozen decoder has 6,459 nodes, 6,460 leaves, 8,391 guarded cases and maximum
depth 34. There are 233 closed cuts, 232 joins, 86 cut files, 15 join files and
one final file. The 102 audits contain 468 named axiom probes and 468 typed
callers. Each new unit uses default Lean proof limits, one thread, 4,096 MiB and
a shared 120-second source/audit budget. The previously checked imported
`SiteCoverage` module has its own historical options; it is an explicit reused
boundary and was not rebuilt by these checks.

Every join needs both actual child theorems. The final `all_sites` theorem covers
the literal imported tree, while `actual_walk_checked` and `actual_walk_exists`
quantify over every finite PC bit list. `consume` retains the decoder's implicit
zero padding/truncation behavior. There is no clean-PC premise. Site execution
soundness comes from the separately checked `SitePrefix246` and simulation
modules; the coverage theorem alone is not a blank-run consistency theorem.

The separate `BinaryPrefix246` module combines this coverage, the actual
410,735-step complete blank bootstrap frame and the calibrated logical seed.
Its intended final statements are external Lean ZF/ZFC calibration theorems.
They do not by themselves give an internal PA derivation or unconditional
nonhalting/consistency.

## Release gate and complete evidence audit

The packer must take the terminal runner record explicitly. It must require
`PASS_COMPLETE_PLAN`, `full_plan = true`, no pending names, exactly the 102
manifest names in `available_records`, and `endpoint_established = true`.
It must then independently validate every selected proof record, rather than
using these summary flags as a substitute for source/object checks:

1. Exact manifest/generation/Site-parent hashes and each source/audit/planned
   guard hash match the frozen plan. The dependency relation is topologically
   closed and the final source still imports the final join.
2. Each selected unit has actual successful source and audit commands, its exact
   expected probe/caller census, only the three permitted standard axioms, equal
   before/after input hashes, and a fresh source object persisted before audit.
   The current source, audit, both snapshots, object, compiler, selected inputs
   and actual first providers match those bytes. Save the observed warning and
   axiom census, including any warnings; do not infer zero from other units.
3. The final `SitesPrefix246` record contains 125 reused project providers: 24
   base prerequisites plus 101 generated ancestors. With its fresh final object,
   all 102 generated coverage modules are accounted for. Each generated object
   must match the selected unit record. Exact DFS imports must reproduce this
   closure; neither filename presence nor a union of unrelated providers is enough.
4. Deduplicate repeated path/hash identities for the final independent review.
   Distinct source/object bytes for the same module are an error. Do not select
   one silently. Hash aliases are accepted only after byte equality is checked.
5. Scan every run/attempt directory and every runner summary in the coverage
   scratch tree. Preserve every terminal PASS, FAIL, TIMEOUT, evidence rejection,
   interrupted attempt and reported precompiler rejection. A current RUNNING
   record must be resolved or explicitly recorded as abandoned, never relabeled
   PASS. Preserve original failure bytes even if later runs succeed. An absence
   of failures is reported only after this final scan.

The three representative cuts (0, 42 and 210) were successfully executed using
`representatives/check-cut*.py`. Their source/audit bytes equal the grouped plan,
but their executed guards are not the planned `guards-four` files. Keep both
identities. Say “102 checked source/audit modules,” not “all 102 manifest guards
were executed.” The remaining selected records should bind their actual guards
from recorded input hashes and their runner command, not a guessed filename.

## Maintained layout

All paths below are relative to the repository. The exact per-module proposed
map is in `publication-plan.json`.

- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SitesPrefix246*.lean`:
  all 102 exact successful source files, including the final endpoint.
- `Computability/BusyBeaver/Research/ZFC/coverage-prefix246/audits/`:
  all 102 exact audits.
- `.../coverage-prefix246/guards/planned/`: 102 exact frozen planned guards.
- `.../coverage-prefix246/attempts/<original-relative-directory>/`:
  raw verification records, exact source/audit logs, actual guard bytes or an
  alias to their single preserved copy, dependency maps, driver logs and any
  distinct failed source/audit snapshots. Successful snapshots with identical
  bytes are aliases of the maintained source/audit rather than extra copies.
- `.../coverage-prefix246/plans/`: exact grouped generation and pipeline
  manifests, reuse lists, source-only single-file/representative plan histories,
  terminal and intermediate runner summaries. Generated plan status strings
  remain the original `GENERATED_SOURCE_ONLY_UNBUILT`; proof status lives in
  the actual proof records, not a rewritten generation manifest.
- `.../coverage-prefix246/programs/`: the exact executed generator, guard
  generator, raw guard template, serial runner, and a separately reviewed portable
  adapter/coordinator. A portable guard-generator variant replaces only the
  template lookup described below; preserve the original next to its diff.
- `.../coverage-prefix246/reviews/`: frozen source-only reviews, final complete
  existing-evidence review, and reported review receipts with their actual scope.
- `.../coverage-prefix246/manifest.json`: one frozen publication manifest with
  every unit, selected attempt, source/audit/guard binding, dependency identity,
  proof budget, probe/caller/axiom/warning census, parent evidence and a content
  registry mapping original paths to published paths and hashes.
- `.../results/prefix246-sites-verification.json`: byte-identical convenience
  copy of the actual final Sites proof record, for the Binary endpoint's parent.
  Both destination aliases are listed explicitly if the raw attempt copy is kept.
- `.../prefix246_coverage.md` and one README paragraph: checked scope, exact
  final theorem, evidence pointers, explicit cache prerequisites and replay recipe.

Do not recursively copy caches or entire per-run histories into every unit.
Publish each unique raw text artifact once, keep aliases in the content registry,
and keep raw JSON records byte-identical. Repeated absolute paths inside historical
records are provenance, not links silently rewritten to new runs. Binary `.olean`
providers remain explicit prerequisites, not published proof certificates.
Do not include this working plan as an independent final-evidence review.

## Reproduction and installed defaults

The generator is deterministic when invoked with the checked grouping:

```
python3 -B generate_sites_prefix246.py --repo REPO --output NEW_PLAN \
  --max-guards 64 --joins-per-module 16 --cuts-per-module 4 \
  --max-batch-guards 128
```

Compare all 102 source/audit bytes and the structural generation data with the
frozen plan. Do not call this a proof run.

The current guard generator reads
`/tmp/zfc-prefix250-lean/coverage/check.py`. Include those exact template bytes
(SHA-256 in the JSON plan). A portable copy should change only that template
lookup to `Path(__file__).with_name('coverage-guard-template.py')`. It can then
regenerate guards with explicit plan/output/Site-evidence arguments. Preserve
original generator, portable variant and exact diff. Do not depend on an
unpublished scratch template or execute the old 250 guard.

The installed coordinator belongs in `Computability/BusyBeaver/Research/ZFC/`,
so `HERE.parents[3]` is the repository root. It must verify the frozen publication
manifest and stage a separate portable execution manifest in a new external
output directory. For each planned guard it may replace only the two default
source/audit path expressions with installed locations; keep source/audit hashes,
provider pins, budgets, audit rules and control flow unchanged. Record each raw
and staged guard hash and the exact defaults-only diff. Runner source may remain
unchanged with explicit `--repo`, `--manifest`, `--manifest-sha`, `--output`,
`--max-units` and `--wall-seconds` arguments. The portable execution manifest must
have its own identity; never overwrite the historical frozen manifest.

There are two intentionally distinct no-proof checks:

- The existing runner's `--prepare-only` validates the plan and any supplied
  successful reuse records but invokes zero per-unit guards. This must remain
  `PREPARED_NO_EXECUTION` and must not be described as 102 guard preparations.
- A stronger installed-default coordinator preparation can invoke each staged
  guard with `--prepare-only`, using exact historical PASS records for its direct
  generated dependencies. Every leaf must remain `PREPARED_NOT_BUILT` with
  `commands=[]`, `fresh_modules=[]`, no version call and no dependency build.
  The coordinator then has 102 Python preparation commands, not `commands=[]`.
  These preparations must remain outside the frozen publication manifest.

Actual replay runs serially, starts with no reused generated proof modules, and
uses each newly produced predecessor PASS when building later dependency maps.
It may be split into bounded sessions using validated reuse lists. One source
plus audit consumes at most 120 seconds; the existing runner accepts at most
3,600 seconds per session. Keep the budget explicit, stop on failure, and retain
all attempts. A zero-new-unit reuse validation is not a fresh proof replay.

These guards reuse exact parent objects recorded in the MP254 and Site246
records. Historical source/object paths must still exist and match, or those
prerequisites must be separately rebuilt and newly pinned through their own
reviewed workflows. Publishing source files and portable defaults does not make
an arbitrary clean checkout a self-contained build. Do not rewrite old JSON
records to impersonate a new cache. Dependency bootstrap/build work remains
outside this packet.

## Parent freeze and final publication order

1. Finish the exact 102-unit proof plan and freeze the terminal summary and final
   Sites proof record. Perform the complete existing-evidence review above.
2. Freeze the Binary guard successor by replacing exactly its three pending
   parent digests with Runtime, BootstrapFrame run2 and final Sites PASS digests.
   The source, audit and 230-module expected list remain unchanged. Preserve the
   pending guard and generator as development history. See `endpoint-freeze.json`.
3. Root may prepare and run that successor guard using scratch sources and exact
   parent records before publication. The final Binary source has nine probes
   and nine callers, default limits, one thread, 4,096 MiB and shared 120 seconds.
4. Root reviews and runs the no-proof packet builder, copies the exact file map,
   and performs installed-default preparation. Save its record and independent
   supplement separately as `results/prefix246-sites-maintained-preparation.json`
   and `results/prefix246-sites-maintained-preparation-review.json`. Keep the
   frozen publication manifest byte-identical.
5. Publish the coverage and Binary result with accurate final theorem status.
   The final Binary PASS is still required before advertising exact246 external
   consistency calibration. Its PA internalization is separate work.
