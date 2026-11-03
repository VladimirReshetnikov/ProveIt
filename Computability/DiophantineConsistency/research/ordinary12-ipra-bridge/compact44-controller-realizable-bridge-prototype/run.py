#!/usr/bin/env python3
"""Bounded single-author attempt joining controller and conditional variation."""
from hashlib import sha256
from pathlib import Path
from shutil import copyfile
import json
import os
import subprocess
import time

HERE = Path(__file__).resolve().parent
BRIDGE = HERE.parent
TEMP = Path('/tmp/ipra-compact44-symbolic-unit-join')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGES = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
OBS = HERE / 'observations'
source = HERE / 'ChosenRankIfRealizable.lean'
frozen = TEMP / 'src/ChosenRankIfRealizable.lean'
obj = TEMP / 'lib/ChosenRankIfRealizable.olean'
prior = [
    ('ChosenControllerCalibration', BRIDGE / 'compact44-chosen-controller-calibration-prototype/observations/terminal.json'),
    ('CompactRankVariationRetry', BRIDGE / 'compact44-conditional-rank-variation-prototype/observations/retry.json'),
]
def sha(p):
    return sha256(p.read_bytes()).hexdigest()
if OBS.exists() or frozen.exists() or obj.exists() or obj.is_symlink():
    raise SystemExit('Refusing to overwrite a prior observation')
inputs = {}
for name, path in prior:
    rec = json.loads(path.read_text())
    if rec['exit_code'] != 0 or sha(TEMP / 'lib' / (name + '.olean')) != rec['object_sha256']:
        raise SystemExit(f'Earlier object missing or changed: {name}')
    inputs[name] = rec['object_sha256']
OBS.mkdir()
copyfile(source, frozen)
env = os.environ.copy()
for key in ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'LD_AUDIT'):
    env.pop(key, None)
env['LEAN_PATH'] = f'{TEMP / "lib"}:{PACKAGES}'
deps = subprocess.run([str(LEAN), '--deps', str(frozen)], env=env,
                      stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
(OBS / 'deps').write_bytes(deps.stdout)
(OBS / 'deps.stderr').write_bytes(deps.stderr)
if deps.returncode != 0 or deps.stderr:
    raise SystemExit('Dependency scan failed')
command = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={TEMP / "src"}',
           str(frozen), '-o', str(obj)]
start = time.monotonic()
try:
    cp = subprocess.run(command, env=env, stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT, timeout=180, check=False)
    code, content = cp.returncode, cp.stdout
except subprocess.TimeoutExpired as ex:
    code, content = None, ex.stdout or b''
log = OBS / 'compile.log'
log.write_bytes(content)
record = dict(command=command, exit_code=code, duration_seconds=round(time.monotonic()-start, 3),
              source_sha256=sha(frozen), log_sha256=sha(log), inputs=inputs,
              object_sha256=sha(obj) if code == 0 and obj.exists() else None,
              warning_present=b'warning:' in content, sorry_present=b'sorryAx' in content,
              scope='Incremental author-side attempt; inherited provider ancestry.')
(OBS / 'terminal.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
print(json.dumps(record, indent=2, sort_keys=True))
if code != 0 or b'error:' in content or b'sorryAx' in content or not obj.exists():
    raise SystemExit(code if code not in (None, 0) else 1)
