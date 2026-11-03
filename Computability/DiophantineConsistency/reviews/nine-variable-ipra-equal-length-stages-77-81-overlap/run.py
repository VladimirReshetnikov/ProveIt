#!/usr/bin/env python3
"""Run guarded stages 77–81 singly while sampling available memory/Lean overlap."""
import json
from pathlib import Path
import subprocess
import sys
import time

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
DC = HERE.parents[1]
RUNNER = DC / 'research/nine-variable-ipra/bounded-build-preflight/replay.py'
OVERLAY = Path('/tmp/nine-ipra-guarded-verify-20261102-a')
OUT = HERE / 'observations/run-attempt01'
OUT.mkdir(parents=True, exist_ok=False)


def snapshot():
    fields = {}
    for line in Path('/proc/meminfo').read_text().splitlines():
        key, _, rest = line.partition(':')
        if key in ('MemAvailable', 'MemTotal', 'SwapFree'):
            fields[key + '_kib'] = int(rest.split()[0])
    if 'MemAvailable_kib' not in fields: raise RuntimeError('missing available-memory reading')
    children = []
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit(): continue
        try:
            argv = (proc / 'cmdline').read_bytes().split(b'\0')
            if not argv or Path(argv[0].decode(errors='replace')).name != 'lean': continue
            status = (proc / 'status').read_text()
            rss = next((line for line in status.splitlines() if line.startswith('VmRSS:')), None)
            children.append({'pid': int(proc.name), 'rss': rss,
                             'argv': [x.decode(errors='replace') for x in argv if x]})
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
    fields['lean_processes'] = sorted(children, key=lambda x: x['pid'])
    fields['time_unix_ns'] = time.time_ns()
    return fields


for stage in range(77, 82):
    receipts = sorted((OVERLAY / 'receipts').glob('*.json'))
    if len(receipts) != stage - 1: raise RuntimeError(('unexpected contiguous stage count', stage, len(receipts)))
    stage_dir = OUT / f'{stage:03d}'; stage_dir.mkdir()
    initial = snapshot()
    if initial['MemAvailable_kib'] < 8 * 1024**2 or len(initial['lean_processes']) > 1:
        (stage_dir / 'preflight-rejected.json').write_text(json.dumps(initial, indent=2, sort_keys=True) + '\n')
        raise RuntimeError(('memory/Lean-process preflight rejected', stage))
    command = [sys.executable, '-I', '-S', '-B', str(RUNNER), '--output', str(OVERLAY), '--limit', '1']
    samples = [initial]
    with (stage_dir / 'stdout').open('xb') as stdout, (stage_dir / 'stderr').open('xb') as stderr:
        proc = subprocess.Popen(command, cwd=ROOT, stdout=stdout, stderr=stderr)
        while proc.poll() is None:
            time.sleep(2)
            samples.append(snapshot())
        code = proc.wait()
    samples.append(snapshot())
    result = {'stage': stage, 'command': command, 'exit_code': code, 'samples': samples,
              'minimum_sampled_available_kib': min(x['MemAvailable_kib'] for x in samples),
              'max_sampled_lean_processes': max(len(x['lean_processes']) for x in samples)}
    (stage_dir / 'terminal.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print('FINISHED_STAGE', stage, 'exit', code, 'minimum_available_kib', result['minimum_sampled_available_kib'],
          'max_lean_processes', result['max_sampled_lean_processes'], flush=True)
    if (code != 0 or result['max_sampled_lean_processes'] > 2 or
            result['minimum_sampled_available_kib'] < 8 * 1024**2):
        raise RuntimeError(('stage failed or sampled resource boundary crossed; no next stage', stage))
print('ALL_FIVE_STAGES_FINISHED')
