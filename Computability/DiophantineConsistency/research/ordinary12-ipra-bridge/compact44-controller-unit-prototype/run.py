#!/usr/bin/env python3
"""Single-side exploratory compile using a previously built controller provider."""
from hashlib import sha256
from pathlib import Path
from shutil import copyfile
import json
import os
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = Path('/tmp/ipra-compact44-unit-explore')
PROVIDER = Path('/tmp/pell-class-simp-188/final')
PACKAGES = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SOURCE = HERE / 'ArithmeticConstructionUnitCompact44.lean'
IMPORTED = ROOT / 'lib/DiophantineConsistency/ArithmeticControllerDataCompact44.olean'
OUT = ROOT / 'ArithmeticConstructionUnitCompact44.olean'
LOG = HERE / 'observations/compile.log'
RECEIPT = HERE / 'observations/terminal.json'

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

ROOT.mkdir(parents=True, exist_ok=True)
source_copy = ROOT / SOURCE.name
copyfile(SOURCE, source_copy)
OUT.unlink(missing_ok=True)
env = os.environ.copy()
for key in ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'LD_AUDIT'):
    env.pop(key, None)
env['LEAN_PATH'] = ':'.join(map(str, (ROOT / 'lib', PROVIDER, PACKAGES)))
cmd = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={ROOT}',
       str(source_copy), '-o', str(OUT)]
observed = {str(p): digest(p) for p in (SOURCE, IMPORTED, LEAN)}
started = time.monotonic()
try:
    cp = subprocess.run(cmd, env=env, stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT, timeout=180, check=False)
    code = cp.returncode
    output = cp.stdout
except subprocess.TimeoutExpired as ex:
    code = None
    output = ex.stdout or b''
LOG.write_bytes(output)
receipt = dict(command=cmd, provider=str(PROVIDER), packages=str(PACKAGES),
               input_sha256=observed, duration_seconds=round(time.monotonic()-started, 3),
               exit_code=code, log_sha256=digest(LOG),
               source_after_sha256=digest(SOURCE), imported_after_sha256=digest(IMPORTED),
               object_sha256=digest(OUT) if code == 0 and OUT.exists() else None,
               scope='Single-side exploratory compile; transitive and package ancestry inherited.')
RECEIPT.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(json.dumps(receipt, indent=2, sort_keys=True))
raise SystemExit(code if code is not None else 124)
