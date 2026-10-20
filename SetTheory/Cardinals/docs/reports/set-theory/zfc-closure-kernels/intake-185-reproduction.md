# Recovering and replaying batches 184–185

The three original packages remain in Git at their arrival commits. The
[batch-184 map](data/intake184-placement.json) and
[batch-185 map](data/intake185-placement.json) account for all 366 original
members. New ancillary files are placed under source prefixes 137–139;
unchanged duplicates refer to existing targets or recorded historical ZIPs.
Main articles, their PDFs and delivery READMEs are archive-only under the
reconciliation-note intake procedure. No original material has become
unrecoverable through retirement of the incoming ZIPs.

Run from the repository root, with two new scratch directories outside it:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake185.py /tmp/zfc185-packets
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/replay-intake185.py --packets /tmp/zfc185-packets --output /tmp/zfc185-replay
```

Choose unused names if either directory exists. Recovery requires local Git
history containing arrivals `a27b5391bb`, `7677a1f62f` and `bf01dd349a`.
It restores the original wrapper directories, including vendored dependencies,
checks ZIP paths, refuses to overwrite an output directory, and executes
nothing. The intake freshly exercised recovery: 191 + 102 + 73 members.

Replay copies the two 220 packages again, unpacks the included immediate K221
parent, and runs 13 selected checks with the standard Python library and
assertions enabled. It writes new logs, rebuilt machines, runtime cases and
`actual.json` under the requested output. The full runtime has a 1,200-second
cap; the other jobs each have a 120-second cap. A failure or timeout stops the
run and retains its record. Do not invoke Python with `-O`.

The wrapper covers construction, canonicalization/startup, full symbolic
runtime and independent runtime audit; then three alternative constructions,
macro equivalence, three independent window checks, three canonical/startup
checks and independent core audit. It compares rebuilt machine/source bytes
with the original releases. It does not run supplied checksum-manifest
wrappers, recursive ancestor suites, proof assistants, or exploratory searches.
The 221 alternatives of batch 184 are recovered but not rerun by this wrapper.

## What was run during intake

The selected commands were first executed using two scratch orchestration
scripts, now consolidated into the reusable replay wrapper above. Their
original absolute `/tmp/zfc-intake185/...` paths are retained in the historical
receipts; these are recorded execution locations, not required public paths.
All 13 jobs passed. The full final runtime took about 144 seconds on the intake
host. It completed all 6,167 cases and 1,516,421 symbolic rules. The separately
run recovery helper reproduced all 366 package members.

- [Construction job record](data/intake185-fresh-construction/actual.json),
  [runtime](data/intake185-fresh-construction/runtime/runtime.json),
  [independent audit](data/intake185-fresh-construction/independent-audit.json).
- [Alternative job record](data/intake185-fresh-alternatives/actual.json),
  [macro proof](data/intake185-fresh-alternatives/macro-diamonds.json),
  [independent audit](data/intake185-fresh-alternatives/independent-core.json).

These new directories hold intake-generated outputs. Files with `138-k220-`
and `139-k220a-` prefixes remain delivered evidence and have not been
rewritten with the intake's timings or paths. The complete runtime case lists
are retained beside their summaries. Fresh evidence supports the ordinary
simulation claims; no newly checked Lean/PA endpoint follows from it.

## Layout and supplementary files

Flattened placement names are archival. Delivered programs still refer to
original relative names such as `portable/`, `machine/`, `verification/`,
`research/` and `vendor/`. Recover the original package before running them;
do not run flattened scripts in the report's `code/` directory. Main report
build scripts also require archive-only TeX inputs. Secondary research scripts
may name the author's old workspace or unshipped search trees and are not
promised to be standalone drivers. Selected final exploratory tables have
literal reconstruction recipes, but such reconstruction is not a proof of
runtime correctness or source equivalence.

Licensing and inherited credits are preserved in the source notices and
recursive parent packages. The new public [220-state publication](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k220/README.md)
includes the exact tables, source, canonical mapping and attribution. No
checksum-manifest audit or line-ending normalization is part of this intake.
