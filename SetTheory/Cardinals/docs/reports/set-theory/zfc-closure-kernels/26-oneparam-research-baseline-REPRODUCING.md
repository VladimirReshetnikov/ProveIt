# Offline reproduction of the public-machine experiments

Run the commands below from the root of the extracted report archive. Python
3.10 or later and its standard library suffice; the audit was executed with
Python 3.12. Do not pass `-O`: the imported attributed helpers use assertions
for input and interface checks. No network access, package installation, Coq,
Lean, or external `paths.json` is used by these commands.

The baseline replay needs the directory structure recorded in
`research/baseline/manifest.json`. In particular, keep both
`helpers/context_search.py` and `helpers/analyze_table.py`, the M253 generator,
the two literal tables, `Prog254.v`, and the unchanged `symexec.py` at their
listed relative paths. The driver resolves these relative to its own file,
so the current directory after launch does not affect module lookup. The
older `04-machine-engineering-*.py` inspection copies are not runtime
inputs to either new search. The manifest lists the exact replay inputs
and original evidence rather than every source inspected for the report.

## 1. Verify inputs and make a disposable replay copy

This preserves the delivered evidence. The copied mixed-search output has a
wall-clock duration and may order a protected-row list differently between
Python hash seeds, so a rerun is not expected to reproduce the raw JSON byte
hash. Its input hashes, choices, outcomes, and normalized per-candidate
records should agree.

```sh
python3 - <<'PY'
from pathlib import Path
import hashlib
import json
import shutil
source = Path('research/baseline')
replay = Path('build/baseline-replay')
if replay.exists():
    raise SystemExit('Choose a fresh replay directory; build/baseline-replay exists.')
manifest = json.loads((source / 'manifest.json').read_text())
for relative, expected in manifest.items():
    raw = (source / relative).read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != expected:
        raise SystemExit(f'Input hash mismatch: {relative}')
for relative in manifest:
    target = replay / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source / relative, target)
shutil.copyfile(source / 'manifest.json', replay / 'manifest.json')
print(f'Verified and copied {len(manifest)} files to {replay}.')
PY
```

## 2. Check the literal table and reproduce the two macro runs

`--source-url` records provenance only; the auditor does not fetch it.

```sh
python3 -I -B build/baseline-replay/busy-beaver/ZF/m253/tools/generate_candidate.py --check

python3 -I -B build/baseline-replay/audit_tm.py \
  build/baseline-replay/busy-beaver/ZF/m253/machine/zfc_253.tm \
  --expected-sha256 84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95 \
  --expected-states 253 --expected-halt 253 \
  --source-commit 0d544f2a2e3c18f12278441a74b7879f31cbe856 \
  --source-url https://github.com/jeff87654/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/machine/zfc_253.tm \
  --window-radius 4 --macro-steps 64 --trace-steps 312975 --self-test \
  --output build/baseline-replay/public253_macro_r4.json

python3 -I -B build/baseline-replay/audit_tm.py \
  build/baseline-replay/busy-beaver/ZF/m253/machine/zfc_253.tm \
  --expected-sha256 84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95 \
  --expected-states 253 --expected-halt 253 \
  --source-commit 0d544f2a2e3c18f12278441a74b7879f31cbe856 \
  --source-url https://github.com/jeff87654/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/machine/zfc_253.tm \
  --window-radius 6 --macro-steps 128 \
  --output build/baseline-replay/public253_macro_r6.json
```

The expected search counts are 31,909/335,369 abstract configurations,
63,756 ordered pairs in each run, and no macro survivor. The first run also
replays the complete 312,975-move finite boot. These are bounded diagnostics,
not new compiler or set-theory proofs.

## 3. Reproduce the mixed-row search and its independent summary

The recorded original run took about 102 seconds; runtime depends on the
host. The summarizer intentionally reads the neighboring raw result file,
which is why the whole replay directory is copied rather than only passing
an alternate `--output` to the driver.

```sh
python3 -I -B build/baseline-replay/mixed_merge_search.py --fuel 1000
python3 -I -B build/baseline-replay/summarize_mixed.py
```

Expected: all 8,391 baseline cases pass, 49,952 construction choices,
886 protected-row rejections, 49,066 affine failures, and no survivors.
The three affine failure categories have counts 44,836 fuel exhaustion,
4,027 symbolic geometry failures, and 203 unexpected terminal statuses.
A fuel limit or an unrepresentable symbolic shape is not a semantic
counterexample to a machine.

## 4. Compare the regenerated evidence

This compares both macro outputs exactly as parsed JSON, the mixed summary
except for the regenerated raw-file digest, and all mixed candidate records
except elapsed wall time and unordered protected-row-list order.

```sh
python3 - <<'PY'
from pathlib import Path
import json
source = Path('research/baseline')
replay = Path('build/baseline-replay')
def read(root, name):
    return json.loads((root / name).read_text())
for name in ('public253_macro_r4.json', 'public253_macro_r6.json'):
    if read(source, name) != read(replay, name):
        raise SystemExit(f'Macro evidence differs: {name}')
a = read(source, 'mixed_merge_summary.json')
b = read(replay, 'mixed_merge_summary.json')
for item in (a, b):
    item.pop('raw_results_sha256')
if a != b:
    raise SystemExit('Mixed summary differs beyond the regenerated raw hash.')
a = read(source, 'mixed_merge_results.json')
b = read(replay, 'mixed_merge_results.json')
for item in (a, b):
    item.pop('elapsed_seconds')
    for candidate in item['candidates']:
        if 'rows' in candidate:
            candidate['rows'].sort()
if a != b:
    raise SystemExit('Normalized per-candidate mixed evidence differs.')
print('Both macro runs and every normalized mixed candidate reproduce.')
PY
```

The commands check the experiment's finite evidence. They do not reproduce
an upstream Coq build, certify the Python affine executor, prove the new
logical interpretation, or establish global state minimality.
