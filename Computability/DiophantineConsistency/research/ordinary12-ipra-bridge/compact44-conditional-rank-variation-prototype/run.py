#!/usr/bin/env python3
"""Bounded same-side generic packing and compact rank-variation attempt."""
from hashlib import sha256
from pathlib import Path
from shutil import copyfile
import json
import os
import subprocess
import time

HERE = Path(__file__).resolve().parent
BRIDGE = HERE.parent
PROJECT = next(p for p in HERE.parents if (p / 'Lean/DiophantineConsistency').is_dir())
TEMP = Path('/tmp/ipra-compact44-symbolic-unit-join')
OBS = HERE / 'observations'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGES = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
if OBS.exists():
    raise SystemExit('Refusing to overwrite prior observations')
prior = json.loads((BRIDGE / 'compact44-symbolic-rank-calibration-prototype/observations/terminal.json').read_text())['stages']
def sha(p):
    return sha256(p.read_bytes()).hexdigest()
if len(prior) != 4 or any(s['exit_code'] != 0 for s in prior):
    raise SystemExit('Missing successful earlier stages')
for stage in prior:
    p = TEMP / 'lib' / (stage['module'] + '.olean')
    if sha(p) != stage['object_sha256']:
        raise SystemExit(f'Earlier object changed: {stage["module"]}')
OBS.mkdir()
modules = [
    ('DiophantineConsistency/ArithmeticPacking', PROJECT / 'Lean/DiophantineConsistency/ArithmeticPacking.lean'),
    ('DiophantineConsistency/ArithmeticConstructionVariationCompact44', HERE / 'ArithmeticConstructionVariationCompact44.lean'),
    ('CompactRankVariation', HERE / 'CompactRankVariation.lean'),
]
env = os.environ.copy()
for k in ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'LD_AUDIT'):
    env.pop(k, None)
env['LEAN_PATH'] = f'{TEMP / "lib"}:{PACKAGES}'
records = []
for module, source in modules:
    name = module.rsplit('/', 1)[-1]
    frozen = TEMP / 'src' / (module + '.lean')
    obj = TEMP / 'lib' / (module + '.olean')
    if frozen.exists() or obj.exists() or obj.is_symlink():
        raise SystemExit(f'Refusing to overwrite {module}')
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
    (OBS / 'terminal.json').write_text(json.dumps(dict(stages=records,
        prior_rank_objects=[s['object_sha256'] for s in prior],
        scope='Incremental author-side build; inherited provider ancestry.'),
        indent=2, sort_keys=True) + '\n')
    print(json.dumps(record, sort_keys=True), flush=True)
    if code != 0 or b'error:' in content or b'sorryAx' in content or not obj.exists():
        raise SystemExit(code if code not in (None, 0) else 1)
