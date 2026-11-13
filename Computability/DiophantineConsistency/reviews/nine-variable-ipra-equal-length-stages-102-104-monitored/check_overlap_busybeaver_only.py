#!/usr/bin/env python3
"""Check the recorded resource samples for the overlapping five-stage run."""
from hashlib import sha256
import json
from pathlib import Path
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
OBS = HERE / 'observations/run-attempt01'
audit = json.loads((HERE / 'observations/stages-102-104/audit.json').read_text())
if audit['status'] != 'EQUAL_LENGTH_PREFIX_SCOPED_COMPARISON_PASS' or audit['upto'] != 104:
    raise RuntimeError('prefix audit not accepted')
rows = []
for stage in range(102, 105):
    folder = OBS / f'{stage:03d}'
    record = json.loads((folder / 'terminal.json').read_text())
    samples = record['samples']
    if (record['stage'] != stage or record['exit_code'] != 0 or not samples or
        (folder / 'stderr').read_bytes() or
        f'PASS {stage} / 104 ' not in (folder / 'stdout').read_text()):
        raise RuntimeError(('stage receipt mismatch', stage))
    minimum = min(s['MemAvailable_kib'] for s in samples)
    maximum = max(len(s['lean_processes']) for s in samples)
    overlap = [s for s in samples if len(s['lean_processes']) == 2 and
               any('/Computability/BusyBeaver/Lean/' in ' '.join(p['argv']) for p in s['lean_processes']) and
               any('/tmp/nine-ipra-guarded-verify-20261102-a/src/' in ' '.join(p['argv']) for p in s['lean_processes'])]
    if (minimum != record['minimum_sampled_available_kib'] or maximum != record['max_sampled_lean_processes'] or
        minimum < 8 * 1024**2 or maximum > 2):
        raise RuntimeError(('resource sample mismatch', stage))
    rows.append({'stage': stage, 'samples': len(samples), 'overlap_samples': len(overlap),
                 'minimum_sampled_available_kib': minimum, 'max_sampled_lean_processes': maximum,
                 'terminal_sha256': sha256((folder / 'terminal.json').read_bytes()).hexdigest()})
print(json.dumps({'status': 'SAMPLED_OVERLAP_102_TO_104', 'rows': rows,
                  'runner_sha256': sha256((HERE / 'run.py').read_bytes()).hexdigest(),
                  'scope': 'two-second /proc samples, not continuous monitoring or a cgroup limit proof'},
                 indent=2, sort_keys=True))
