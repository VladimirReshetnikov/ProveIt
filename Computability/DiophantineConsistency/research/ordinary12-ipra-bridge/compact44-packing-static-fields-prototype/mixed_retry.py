#!/usr/bin/env python3
"""Bounded exploratory mask check, extending the unit provider with word roots."""
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
OBS = HERE / 'observations04'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PKG = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SOURCE = HERE / 'CompactPackingStaticFields.lean'
if ROOT.exists() or OBS.exists():
    raise SystemExit('Refusing to overwrite earlier attempt')
def sha(p):
    return sha256(p.read_bytes()).hexdigest()
def companions(root, name):
    result = {}
    for suffix in ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir'):
        p = root / (name + suffix)
        result[suffix] = sha(p) if p.exists() else None
    return result
overlap_names = ['DiophantineConsistency/CompactSymbolicPorts',
                 'DiophantineConsistency/CompactFixedBeta',
                 'DiophantineConsistency/ArithmeticPow',
                 'DiophantineConsistency/ArithmeticStandardCasts',
                 'DiophantineConsistency/ArithmeticPackingBlocks']
overlap = {n: {'unit': companions(UNIT, n), 'word': companions(WORD, n)} for n in overlap_names}
if any(x['unit'] != x['word'] or x['unit']['.olean'] is None for x in overlap.values()):
    raise SystemExit('Direct overlap or companion mismatch')
chosen = {'unit': companions(UNIT, 'ChosenControllerCalibration'),
          'word': companions(WORD, 'ChosenControllerCalibration')}
if chosen['unit']['.olean'] is None or (chosen['word']['.olean'] is not None and chosen['word'] != chosen['unit']):
    raise SystemExit('Missing chosen object or mismatched overlapping companion')
top_names = sorted(p.name[:-6] for p in UNIT.glob('*.olean') if p.exists())
top_overlap = {n: {'unit': companions(UNIT, n), 'word': companions(WORD, n)} for n in top_names}
if any(x['word']['.olean'] is not None and x['unit'] != x['word'] for x in top_overlap.values()):
    raise SystemExit('Top-level overlapping object or companion mismatch')
(ROOT / 'src').mkdir(parents=True)
(ROOT / 'lib').mkdir()
OBS.mkdir()
for n, p in [('DiophantineConsistency', UNIT / 'DiophantineConsistency'),
             ('BusyBeaver', WORD / 'BusyBeaver'), ('FirstOrder', WORD / 'FirstOrder')]:
    (ROOT / 'lib' / n).symlink_to(p)
for p in UNIT.iterdir():
    if p.is_file():
        (ROOT / 'lib' / p.name).symlink_to(p)
frozen = ROOT / 'src/CompactPackingStaticFields.lean'
obj = ROOT / 'lib/CompactPackingStaticFields.olean'
copyfile(SOURCE, frozen)
env = os.environ.copy()
for key in ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'LD_AUDIT'):
    env.pop(key, None)
env['LEAN_PATH'] = f'{ROOT / "lib"}:{PKG}'
deps = subprocess.run([str(LEAN), '--deps', str(frozen)], env=env,
                      stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
(OBS / 'deps').write_bytes(deps.stdout)
(OBS / 'deps.stderr').write_bytes(deps.stderr)
if deps.returncode != 0 or deps.stderr:
    raise SystemExit('Dependency scan failed')
cmd = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={ROOT / "src"}',
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
              source_sha256=sha(frozen), log_sha256=sha(log), overlap=overlap,
              chosen=chosen, top_overlap=top_overlap,
              object_sha256=sha(obj) if code == 0 and obj.exists() else None,
              warning_present=b'warning:' in content, sorry_present=b'sorryAx' in content,
              scope='Mixed-provider point-in-time overlap; transitive/package/dynamic ancestry inherited.')
(OBS / 'terminal.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
print(json.dumps(record, indent=2, sort_keys=True))
if code != 0 or b'error:' in content or b'sorryAx' in content or not obj.exists():
    raise SystemExit(code if code not in (None, 0) else 1)
