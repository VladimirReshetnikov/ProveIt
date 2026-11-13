#!/usr/bin/env python3
"""Incrementally test an irreducible alias over the existing join provider."""
from hashlib import sha256
from pathlib import Path
from shutil import copyfile
import json
import os
import subprocess
import time

HERE = Path(__file__).resolve().parent
TEMP = Path('/tmp/ipra-compact44-symbolic-unit-join')
OBS = HERE / 'observations03'
OLD = HERE.parent / 'compact44-symbolic-controller-join-prototype/observations/terminal.json'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGES = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
if OBS.exists():
    raise SystemExit('Refusing to overwrite previous observations')
prior = json.loads(OLD.read_text())['stages']
if len(prior) != 5 or any(r['exit_code'] != 0 for r in prior[:4]):
    raise SystemExit('Missing earlier successful stages')
def sha(p):
    return sha256(p.read_bytes()).hexdigest()
for stage in prior[:4]:
    p = TEMP / 'lib' / (stage['module'] + '.olean')
    if sha(p) != stage['object_sha256']:
        raise SystemExit(f'Earlier object changed: {stage["module"]}')
OBS.mkdir()
modules = ['KernelAliasExplicit']
env = os.environ.copy()
for key in ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'LD_AUDIT'):
    env.pop(key, None)
env['LEAN_PATH'] = f'{TEMP / "lib"}:{PACKAGES}'
records = []
for name in modules:
    source = HERE / (name + '.lean')
    frozen = TEMP / 'src' / (name + '.lean')
    obj = TEMP / 'lib' / (name + '.olean')
    if frozen.exists() or obj.exists():
        raise SystemExit(f'Will not overwrite {name}')
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
    record = dict(module=name, command=command, exit_code=code,
                  duration_seconds=round(time.monotonic()-start, 3),
                  source_sha256=sha(frozen), log_sha256=sha(log),
                  object_sha256=sha(obj) if code == 0 and obj.exists() else None,
                  warning_present=b'warning:' in content, sorry_present=b'sorryAx' in content)
    records.append(record)
    receipt = dict(earlier_stage_objects=[r['object_sha256'] for r in prior[:4]],
                   stages=records, scope='Incremental same-side experiment; inherited ancestry.')
    (OBS / 'terminal.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print(json.dumps(record, sort_keys=True), flush=True)
    if code != 0 or b'sorryAx' in content or b'error:' in content or not obj.exists():
        raise SystemExit(code if code not in (None, 0) else 1)
