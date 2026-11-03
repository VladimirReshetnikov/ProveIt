#!/usr/bin/env python3
"""Bounded separated static-field attempts on the previously captured overlay."""
from hashlib import sha256
from pathlib import Path
from shutil import copyfile
import json
import os
import subprocess
import time

HERE = Path(__file__).resolve().parent
UNIT = Path('/tmp/ipra-compact44-symbolic-unit-join/lib')
WORD = Path('/tmp/ipra-compact-word-cell-author-01/lib')
ROOT = Path('/tmp/ipra-compact44-static-mask-mixed02')
OBS = HERE / 'observations06'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PKG = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
if OBS.exists():
    raise SystemExit('Refusing to overwrite earlier attempt')
def sha(p):
    return sha256(p.read_bytes()).hexdigest()
def companions(root, name):
    return {suffix: sha(root / (name + suffix)) if (root / (name + suffix)).exists() else None
            for suffix in ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir')}
prior = json.loads((HERE / 'observations04/terminal.json').read_text())
if prior['exit_code'] == 0:
    raise SystemExit('Unexpected prior status')
for field in ('overlap', 'top_overlap'):
    for name, pair in prior[field].items():
        if companions(UNIT, name) != pair['unit'] or companions(WORD, name) != pair['word']:
            raise SystemExit(f'Previously recorded overlap changed: {name}')
OBS.mkdir()
env = os.environ.copy()
for key in ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'LD_AUDIT'):
    env.pop(key, None)
env['LEAN_PATH'] = f'{ROOT / "lib"}:{PKG}'
geometry = json.loads((HERE / 'observations05/terminal.json').read_text())['stages'][0]
if geometry['exit_code'] != 0 or sha(ROOT / 'lib/CompactPackingGeometry.olean') != geometry['object_sha256']:
    raise SystemExit('Geometry object changed')
names = ['CompactPackingMaskAlgebra', 'CompactSymbolicMaskData', 'CompactSymbolicMaskFields']
records = []
for name in names:
    source = HERE / (name + '.lean')
    frozen = ROOT / 'src' / (name + '.lean')
    obj = ROOT / 'lib' / (name + '.olean')
    if frozen.exists() and name == 'CompactPackingMaskAlgebra' and not obj.exists():
        saved = HERE / 'observations05/CompactPackingMaskAlgebra-attempt01.lean'
        if not saved.exists() or sha(saved) != sha(frozen):
            raise SystemExit('Failed source does not match retained copy')
        frozen.unlink()
    if frozen.exists() or obj.exists() or obj.is_symlink():
        raise SystemExit(f'Refusing to overwrite {name}')
    copyfile(source, frozen)
    deps = subprocess.run([str(LEAN), '--deps', str(frozen)], env=env,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
    (OBS / f'{name}.deps').write_bytes(deps.stdout)
    (OBS / f'{name}.deps.stderr').write_bytes(deps.stderr)
    if deps.returncode != 0 or deps.stderr:
        raise SystemExit(f'Dependency scan failed: {name}')
    cmd = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={ROOT / "src"}',
           str(frozen), '-o', str(obj)]
    start = time.monotonic()
    try:
        cp = subprocess.run(cmd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=180, check=False)
        code, content = cp.returncode, cp.stdout
    except subprocess.TimeoutExpired as ex:
        code, content = None, ex.stdout or b''
    log = OBS / f'{name}.log'
    log.write_bytes(content)
    rec = dict(module=name, command=cmd, exit_code=code,
               duration_seconds=round(time.monotonic()-start, 3), source_sha256=sha(frozen),
               log_sha256=sha(log), object_sha256=sha(obj) if code == 0 and obj.exists() else None,
               warning_present=b'warning:' in content, sorry_present=b'sorryAx' in content)
    records.append(rec)
    (OBS / 'terminal.json').write_text(json.dumps(dict(stages=records,
        prior_receipt_sha256=sha(HERE / 'observations04/terminal.json'),
        scope='Mixed-provider exploratory observation; inherited closure and dynamic ancestry.'),
        indent=2, sort_keys=True) + '\n')
    print(json.dumps(rec, sort_keys=True), flush=True)
    if code != 0 or b'error:' in content or b'sorryAx' in content or not obj.exists():
        raise SystemExit(code if code not in (None, 0) else 1)
