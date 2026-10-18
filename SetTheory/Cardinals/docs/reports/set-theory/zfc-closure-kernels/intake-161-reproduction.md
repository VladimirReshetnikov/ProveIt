# Reproduce batch 161

The [placement map](data/intake-161-placement.json) covers all 283 delivered
files:263 placed ancillary files and 20 archive-only manuscripts/sections/PDFs/
root delivery READMEs. Placement is `c5d81a0d28`. Restore original nested
package names from the committed arrival archives, using a new output outside
the checkout:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover_161.py \
  --repo "$PWD" --output /tmp/zfc-batch161
```

The helper restores `60-beyond/beyond252` and `61-selector/zfc-prefix247`.
It compares placed payloads with their original archive bytes and preserves
archive-only text. It performs no network access, proof build or suite
execution. Checksum manifests are preserved without interpretation. The
[recovery record](data/intake-161-recovery.json) records the independent run.
The source archives remain recoverable at:

| Source | Arrival | Committed archive |
| --- | --- | --- |
| 60 | `e0b512a63e2c1ca6a1698fa437b8568f1643ff6b` | `docs/incoming/beyond252-research.zip` |
| 61 | `96030114f5dbba906e408608e4646057f2111776` | `docs/incoming/zfc-prefix247-research-20261017.zip` |

Run verifiers only in additional writable copies, because they overwrite
results. Use Python 3 with assertions enabled and `PYTHONOPTIMIZE` unset.
The suites use the standard library; no compiler or dependency installation
is required. Root's observed source 60 run passed in 22.727 seconds; source 61's
outer run passed in 17.250 seconds under a 300-second outer bound. These are
observed runtimes, not performance guarantees.

## Source 60: preserve substantive checks, skip manifest verification

The delivered `code/verify_all.py` runs thirteen component jobs plus inline
compound-ledger coverage and two exact altered startups. Intake deliberately
skipped two checksum-only paths: its root manifest function and the two-line
import-manifest loop in `exploratory/verify_layouts.py`. No mathematical,
source/table-binding, runtime, codec or coverage assertion was removed.
The [adaptation record](data/intake-161-source60-adaptations.json) describes
those changes and the root wrapper that captured full subprocess output and
requested JSON before temporary outputs were deleted. Original archive,
extraction and placed sources were unchanged.

For a new run, first copy the recovered `beyond252` package to a new external
directory such as `/tmp/zfc-source60-rerun`. The following command repeats the
two narrow skips and runs the substantive suite, writing a fresh summary:

```sh
python3 -B - /tmp/zfc-source60-rerun /tmp/zfc-source60-rerun-summary.json <<'PY'
from pathlib import Path
import importlib.util, os, sys
if not __debug__:
    raise RuntimeError('Assertions must remain enabled')
root, output = map(lambda s: Path(s).resolve(), sys.argv[1:])
os.environ.pop('PYTHONOPTIMIZE', None)
p = root / 'exploratory/verify_layouts.py'
old = "    manifest=json.loads((HERE/'import_manifest.json').read_text())\n    for path,record in manifest.items():assert sha(HERE/path)==record['sha256'],('changed input',path)\n"
text = p.read_text()
assert text.count(old) == 1, 'Use a fresh copy of the recovered package'
p.write_text(text.replace(old, '    # Intake: skip checksum-manifest verification.\n'))
sys.path.insert(0, str(root / 'code'))
spec = importlib.util.spec_from_file_location('suite60', root / 'code/verify_all.py')
suite = importlib.util.module_from_spec(spec)
spec.loader.exec_module(suite)
suite.verify_manifest = lambda: {'status': 'SKIPPED_BY_USER_INTAKE_INSTRUCTION'}
sys.argv = [str(root / 'code/verify_all.py'), '--output', str(output)]
suite.main()
PY
```

The generic driver prints a line beginning `PASS manifest/...`; that wording
is inherited from the delivered driver. It must not be read as a manifest
check. The actual fresh JSON says
`manifest.status=SKIPPED_BY_USER_INTAKE_INSTRUCTION`.

The [fresh summary](data/intake-161-source60-replay-summary.json) records all 13
component jobs: baseline, semantic seed audit, negation macros, prefill 255
runtime, direct 255 runtime, four zone certificates, baseline synthesis
coverage, direct 255 resumed-ledger coverage, baseline phase follow-up, and
saved scanner-layout replay. Component stdout and requested JSON are retained
under `data/intake-161-source60-` prefixes.

The inline coverage check reconstructs all 55,471 compound-fold recipe identities
and verifies the supplied ledger, explicitly reporting `trace_replayed=false`.
It does not re-execute those full searches. Both 255-state tables are actually
simulated for 82,552 steps to the complete 77-one-cell baseline frame. Fresh
runtime checks cover 7,221 prefill and 7,311 direct cases, under the attributed
imported box contracts. The phase follow-up freshly reran 1,674 recipes and 20,380 cases. Zone
caps 1, 2, 8 and 32 each covered 6,456 live leaves and 8,385 enabled cases,
with the same six excluded cases and one halt case; other complete-ledger checks establish coverage rather than replaying
all historical executions. None is a new kernel proof or a lower bound.

## Source 61: unchanged seven-check suite

Copy recovered `61-selector/zfc-prefix247` to another new external directory,
enter that copy, and run:

```sh
python3 -B code/verify.py
```

Root used that exact command in `/tmp/zfc-intake-161/run61`, with no edits to
any supplied checker. The [outer replay record](data/intake-161-source61-replay.json)
and [fresh summary](data/intake-161-source61-fresh-verification-summary.json)
record seven checks total:

1. Inline inherited 252→250 reconstruction.
2. Exact printed 247 table reconstruction and comparison.
3. All 496 intermediate 248→247 quotient rows and dual sparse/dense 741,241-step startup.
4. Universal prefix/marking induction templates and all 8,391 guarded instructions.
5. Independent complete source parse and full-width-PC audit.
6. Finite literal instructions: 33,564 cases.
7. Finite literal arithmetic: 16,200 cases.

The canonical table has 247 working states, 494 transitions, start 0, dispatcher 89
and separate halt 247. Its identity is
`58bbbda620daf6d4d62f486db05f54d0dccb8373c080c1b5a0b26533e7a3a669`.
The old-label table identity is
`0d37614f3caf37139b0be127837630539224acd1c45d748cf5704abfc3230b42`.
Startup reaches head −5/marker −6/header 245/distance 250, logical registers
`[3,0,0,0,3,0,0,0,0]`, 235 value-one spares and 487 one-cells. Complete support
and blank exteriors are checked. The symbolic returning cases all record
positive progress, with minimum 13 literal transitions.

The [delivery comparison](data/intake-161-source61-replay-comparison.json)
compares nine regenerated artifacts. Bootstrap row visits, macro inductions,
runtime summary, all runtime-case JSONL and full-source JSON are identical.
Bootstrap and the two literal-regression JSONs differ only in their timing
fields. The verification summary additionally changes Python version,
completion timestamp, temporary output directory and runtimes. No mathematical
result differs.

`report-build`, `current-source-audit` and `independent-review` were unchanged
inherited records, not regenerated suite outputs; they are not published as
fresh evidence. The independent reviewer separately compared all 12 supplied
logical source snapshots against both their pinned Git revision and maintained
source. This establishes source identity, not a new proof build.

The [independent source review](intake-161-source-61.md) retains its original
source-only status. Its [root replay supplement](data/intake-161-source61-review-replay-supplement.json)
records the later actual PASS and exact input identities without a reviewer
rerun. The inherited reference 250 bundle remains intact as a dependency;
its code identity does not count as another fresh 250 suite execution.

No intake run invoked Lean/Rocq, proved unconditional nonhalting, rebuilt the
logical calibration, or supplied equivalence inside PA. Finite startup and
literal regressions certify their finite endpoints; universal claims rely on
the stated induction/simulation arguments and the explicitly imported
contracts. Full proof-assistant endpoints for the new tables remain separate.

The retained root replay wrappers in `code/replay_source60_161.py` and
`code/replay_source61_161.py` are historical records with their original scratch
paths. Use the portable commands above for a new run. Fresh stdout/stderr logs
are published as `.txt` files under the corresponding `data/intake-161-`
prefixes; their contents are unchanged. The independent second review is in
[data/intake-161-second-review.json](data/intake-161-second-review.json). Its
editorial finding about six link targets was corrected before publication.
