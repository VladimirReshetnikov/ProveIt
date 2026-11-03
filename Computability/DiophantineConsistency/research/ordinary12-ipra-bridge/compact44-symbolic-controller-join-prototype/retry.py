#!/usr/bin/env python3
"""Retry only the join client over the four earlier same-side objects."""
from hashlib import sha256
from pathlib import Path
from shutil import copyfile
import json
import os
import subprocess
import time

HERE = Path(__file__).resolve().parent
TEMP = Path('/tmp/ipra-compact44-symbolic-unit-join')
OBS = HERE / 'observations'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGES = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SOURCE = HERE / 'CompactSymbolicControllerJoin-DRAFT.lean'
FROZEN = TEMP / 'src/CompactSymbolicControllerJoinRetry.lean'
OBJ = TEMP / 'lib/CompactSymbolicControllerJoinRetry.olean'
LOG = OBS / 'CompactSymbolicControllerJoinRetry.log'
RECEIPT = OBS / 'retry.json'
prior = json.loads((OBS / 'terminal.json').read_text())['stages']
if len(prior) != 5 or any(r['exit_code'] != 0 for r in prior[:4]) or prior[4]['exit_code'] == 0:
    raise SystemExit('Unexpected earlier stage results')
if any(p.exists() for p in (FROZEN, OBJ, LOG, RECEIPT)):
    raise SystemExit('Refusing to overwrite previous retry')
def sha(path):
    return sha256(path.read_bytes()).hexdigest()
for stage in prior[:4]:
    obj = TEMP / 'lib' / (stage['module'] + '.olean')
    if sha(obj) != stage['object_sha256']:
        raise SystemExit(f'Earlier output changed: {stage["module"]}')
copyfile(SOURCE, FROZEN)
env = os.environ.copy()
for key in ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'LD_AUDIT'):
    env.pop(key, None)
env['LEAN_PATH'] = f'{TEMP / "lib"}:{PACKAGES}'
command = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={TEMP / "src"}',
           str(FROZEN), '-o', str(OBJ)]
start = time.monotonic()
try:
    cp = subprocess.run(command, env=env, stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT, timeout=180, check=False)
    code, content = cp.returncode, cp.stdout
except subprocess.TimeoutExpired as ex:
    code, content = None, ex.stdout or b''
LOG.write_bytes(content)
record = dict(command=command, exit_code=code, duration_seconds=round(time.monotonic()-start, 3),
              source_sha256=sha(FROZEN), log_sha256=sha(LOG),
              earlier_stage_objects=[r['object_sha256'] for r in prior[:4]],
              object_sha256=sha(OBJ) if code == 0 and OBJ.exists() else None,
              warning_present=b'warning:' in content, sorry_present=b'sorryAx' in content,
              scope='Incremental same-side retry; inherited provider and package ancestry.')
RECEIPT.write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
print(json.dumps(record, indent=2, sort_keys=True))
if code != 0 or b'sorryAx' in content or b'error:' in content or not OBJ.exists():
    raise SystemExit(code if code not in (None, 0) else 1)
