#!/usr/bin/env python3
"""Incremental author-side controller-choice and calibration build."""
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
OBS = HERE / 'observations'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGES = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
if OBS.exists():
    raise SystemExit('Refusing to overwrite observations')
unit_data = json.loads((BRIDGE / 'compact44-controller-abstract-bridge-prototype/observations/terminal.json').read_text())
unit_stages = unit_data['stages']
if len(unit_stages) != 4 or any(r['exit_code'] != 0 for r in unit_stages):
    raise SystemExit('Missing successful symbolic-unit stages')
def sha(p):
    return sha256(p.read_bytes()).hexdigest()
for stage in unit_stages:
    obj = TEMP / 'lib' / (stage['module'] + '.olean')
    if sha(obj) != stage['object_sha256']:
        raise SystemExit(f'Unit output changed: {stage["module"]}')
OBS.mkdir()
modules = [('DiophantineConsistency/CompactControllerTriangle', 'CompactControllerTriangle'),
           ('DiophantineConsistency/ArithmeticControllerChoiceCompact44Triangle', 'ArithmeticControllerChoiceCompact44Triangle'),
           ('AliasRankCalibration', 'AliasRankCalibration'),
           ('ActualRankCalibration', 'ActualRankCalibration')]
env = os.environ.copy()
for key in ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'LD_AUDIT'):
    env.pop(key, None)
env['LEAN_PATH'] = f'{TEMP / "lib"}:{PACKAGES}'
records = []
for module, name in modules:
    source = HERE / (name + '.lean')
    frozen = TEMP / 'src' / (module + '.lean')
    obj = TEMP / 'lib' / (module + '.olean')
    if frozen.exists() or obj.exists() or obj.is_symlink():
        raise SystemExit(f'Will not overwrite {module}')
    copyfile(source, frozen)
    deps = subprocess.run([str(LEAN), '--deps', str(frozen)], env=env,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
    (OBS / f'{name}.deps').write_bytes(deps.stdout)
    (OBS / f'{name}.deps.stderr').write_bytes(deps.stderr)
    if deps.returncode != 0 or deps.stderr:
        raise SystemExit(f'Dependency scan failed for {name}')
    command = [str(LEAN), '-M3000', '-j1', '-DElab.async=false',
               f'--root={TEMP / "src"}', str(frozen), '-o', str(obj)]
    start = time.monotonic()
    try:
        cp = subprocess.run(command, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=180, check=False)
        code, content = cp.returncode, cp.stdout
    except subprocess.TimeoutExpired as ex:
        code, content = None, ex.stdout or b''
    log = OBS / f'{name}.log'
    log.write_bytes(content)
    record = dict(module=module, command=command, exit_code=code,
                  duration_seconds=round(time.monotonic()-start, 3),
                  source_sha256=sha(frozen), log_sha256=sha(log),
                  object_sha256=sha(obj) if code == 0 and obj.exists() else None,
                  warning_present=b'warning:' in content, sorry_present=b'sorryAx' in content)
    records.append(record)
    receipt = dict(unit_objects=[r['object_sha256'] for r in unit_stages],
                   stages=records, scope='Incremental author-side build; inherited provider ancestry.')
    (OBS / 'terminal.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print(json.dumps(record, sort_keys=True), flush=True)
    if code != 0 or b'sorryAx' in content or b'error:' in content or not obj.exists():
        raise SystemExit(code if code not in (None, 0) else 1)
