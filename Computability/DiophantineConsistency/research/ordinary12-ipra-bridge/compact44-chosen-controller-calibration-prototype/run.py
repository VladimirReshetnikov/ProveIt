#!/usr/bin/env python3
"""One bounded chosen-dimensions client on the existing symbolic provider."""
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
source = HERE / 'ChosenControllerCalibration.lean'
frozen = TEMP / 'src/ChosenControllerCalibration.lean'
obj = TEMP / 'lib/ChosenControllerCalibration.olean'
prior = json.loads((BRIDGE / 'compact44-symbolic-rank-calibration-prototype/observations/terminal.json').read_text())['stages']
def sha(p):
    return sha256(p.read_bytes()).hexdigest()
if OBS.exists() or frozen.exists() or obj.exists() or obj.is_symlink():
    raise SystemExit('Refusing to overwrite a prior observation')
if len(prior) != 4 or any(r['exit_code'] != 0 for r in prior):
    raise SystemExit('Missing preceding rank calibration stages')
for stage in prior:
    if sha(TEMP / 'lib' / (stage['module'] + '.olean')) != stage['object_sha256']:
        raise SystemExit(f'Earlier object changed: {stage["module"]}')
OBS.mkdir()
copyfile(source, frozen)
env = os.environ.copy()
for k in ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'LD_AUDIT'):
    env.pop(k, None)
env['LEAN_PATH'] = f'{TEMP / "lib"}:{PACKAGES}'
deps = subprocess.run([str(LEAN), '--deps', str(frozen)], env=env,
                      stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
(OBS / 'deps').write_bytes(deps.stdout)
(OBS / 'deps.stderr').write_bytes(deps.stderr)
if deps.returncode != 0 or deps.stderr:
    raise SystemExit('Dependency scan failed')
cmd = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={TEMP / "src"}',
       str(frozen), '-o', str(obj)]
start = time.monotonic()
try:
    cp = subprocess.run(cmd, env=env, stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT, timeout=180, check=False)
    code, content = cp.returncode, cp.stdout
except subprocess.TimeoutExpired as ex:
    code, content = None, ex.stdout or b''
log = OBS / 'compile.log'
log.write_bytes(content)
record = dict(command=cmd, exit_code=code, duration_seconds=round(time.monotonic()-start, 3),
              source_sha256=sha(frozen), log_sha256=sha(log),
              previous_objects=[s['object_sha256'] for s in prior],
              object_sha256=sha(obj) if code == 0 and obj.exists() else None,
              warning_present=b'warning:' in content, sorry_present=b'sorryAx' in content,
              scope='Incremental author-side build; inherited provider ancestry.')
(OBS / 'terminal.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
print(json.dumps(record, indent=2, sort_keys=True))
if code != 0 or b'sorryAx' in content or b'error:' in content or not obj.exists():
    raise SystemExit(code if code not in (None, 0) else 1)
