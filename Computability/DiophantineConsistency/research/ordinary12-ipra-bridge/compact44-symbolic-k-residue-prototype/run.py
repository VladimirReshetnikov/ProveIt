#!/usr/bin/env python3
"""Run one bounded, single-author Horner draft observation; no closure audit."""
from hashlib import sha256
from pathlib import Path
from shutil import copyfile
import json
import os
import re
import subprocess
import sys
import time

if len(sys.argv) != 2 or re.fullmatch(r'[0-9]{2}', sys.argv[1]) is None:
    raise SystemExit('Pass an unused two-digit attempt number')
label = sys.argv[1]
here = Path(__file__).resolve().parent
outdir = here / 'observations'
outdir.mkdir(exist_ok=True)
log = outdir / f'attempt{label}.log'
snapshot = outdir / f'attempt{label}.lean'
receipt = outdir / f'attempt{label}.json'
if any(p.exists() for p in (log, snapshot, receipt)):
    raise SystemExit('Attempt already exists')
source = here / 'SymbolicKernelResidue.lean'
tmp = Path('/tmp/ipra-compact44-k-horner-explore')
tmp.mkdir(exist_ok=True)
build_source = tmp / 'SymbolicKernelResidue.lean'
copyfile(source, snapshot)
copyfile(source, build_source)
obj = tmp / 'SymbolicKernelResidue.olean'
obj.unlink(missing_ok=True)
provider = Path('/tmp/compact44-k-radix-cert-01/lib')
packages = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
lean = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
imported = provider / 'DiophantineConsistency/CompactSymbolicKernelOpaque.olean'
def sha(p):
    return sha256(p.read_bytes()).hexdigest()
env = os.environ.copy()
for key in ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'LD_AUDIT'):
    env.pop(key, None)
env['LEAN_PATH'] = f'{provider}:{packages}'
cmd = [str(lean), '-M3000', '-j1', '-DElab.async=false', f'--root={tmp}',
       str(build_source), '-o', str(obj)]
before = {str(p): sha(p) for p in (snapshot, imported, lean)}
start = time.monotonic()
try:
    result = subprocess.run(cmd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=180, check=False)
    code, output = result.returncode, result.stdout
except subprocess.TimeoutExpired as ex:
    code, output = None, ex.stdout or b''
log.write_bytes(output)
record = dict(command=cmd, provider=str(provider), packages=str(packages),
              input_sha256=before, imported_after_sha256=sha(imported),
              duration_seconds=round(time.monotonic()-start, 3), exit_code=code,
              log_sha256=sha(log), object_sha256=sha(obj) if code == 0 and obj.exists() else None,
              scope='Single-author observation; transitive and package ancestry inherited.')
receipt.write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
print(json.dumps(record, indent=2, sort_keys=True))
raise SystemExit(code if code is not None else 124)
