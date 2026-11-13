#!/usr/bin/env python3
"""Run the prepared closure sequentially; never reuse any of its objects."""
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path('/tmp/p65-post-merge-replay')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LEAN_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


if sha(LEAN) != LEAN_SHA:
    raise SystemExit('unexpected Lean binary')
plan = json.loads((ROOT / 'plan.json').read_text())
if len(plan) != 8:
    raise SystemExit('unexpected plan size')
for e in plan:
    if sha(Path(e['source'])) != e['source_sha256'] or sha(Path(e['shim'])) != e['shim_sha256']:
        raise SystemExit(f'source or shim changed: {e["module"]}')
    if Path(e['object']).exists() or Path(e['object']).is_symlink():
        raise SystemExit(f'output already exists; refusing cache reuse: {e["module"]}')
if (ROOT / 'results.json').exists():
    raise SystemExit('existing run record; refusing overwrite')

env = os.environ.copy()
env['LEAN_PATH'] = ':'.join([str(ROOT / 'lib'), '/tmp',
    '/tmp/trace74-direct-four-block-1zltaw2f/lib',
    '/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'])
(ROOT / 'logs').mkdir()
records = []
for e in plan:
    command = [str(LEAN), '-M6000', '-j1', '-DElab.async=false',
               '--root=' + str(ROOT / 'src'), e['shim'], '-o', e['object']]
    print('Compiling', e['module'], flush=True)
    start = time.monotonic()
    try:
        run = subprocess.run(command, env=env, text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, timeout=300)
        output, code = run.stdout, run.returncode
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or b'').decode(errors='replace') if isinstance(exc.stdout, bytes) else (exc.stdout or '')
        output += '\nTimed out after 300 seconds.\n'
        code = 124
    log = ROOT / 'logs' / (e['module'] + '.txt')
    log.write_text(output)
    record = {'module': e['module'], 'command': command, 'exit': code,
              'elapsed_seconds': round(time.monotonic() - start, 3),
              'source_sha256': e['source_sha256'], 'shim_sha256': e['shim_sha256'],
              'log': str(log), 'log_sha256': sha(log),
              'object': e['object'], 'object_sha256': sha(Path(e['object'])) if code == 0 else None}
    records.append(record)
    (ROOT / 'results.json').write_text(json.dumps(records, indent=2) + '\n')
    if code or 'sorryAx' in output or 'error:' in output:
        print(f'FAILED {e["module"]} (exit {code}); see {log}', flush=True)
        print(output[-4000:], flush=True)
        sys.exit(1)
print('PASS: all eight affected modules recompiled with no sorryAx or errors.', flush=True)
